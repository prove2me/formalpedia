-- Prove2me | Theorems.Thm_ShortBroadcastDom_Supplement_theorem_A
-- name    : ShortBroadcastDom.Supplement.theorem_A
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T23:42:53.106672+00:00
-- url     : https://prove2.me/theorems/0e876b26-49f8-478c-bedb-96849c29578b
-- title:
--   Theorem A — constant-round $(1+\delta)$-approximate fractional covers for general covering relations on $\mathcal C_\rho$
-- statement:
--   Fix rationals $\rho\ge1$ and $\delta>0$ and an integer $b\ge1$. There is a deterministic broadcast CONGEST algorithm with a constant number of rounds (depending only on $\rho,\delta,b$) with the following guarantee. Let $G\in\mathcal C_\rho$, let $R\subseteq V(G)$ be the demands, let every demand $r$ have a nonempty covering set $C(r)\subseteq N_G[r]$, and let the costs satisfy $c_v\in\{1,\dots,b\}$; every vertex knows only its identifier, its demand bit, its cost and the incidence information of the covering relation. Then the algorithm outputs a vector $x\ge0$, supported on the vertices that belong to some covering set, with
--
--   $$
--   \sum_{v\in C(r)}x_v\ge1\quad(r\in R),\qquad \sum_v c_vx_v\le(1+\delta)\,\tau_c .
--   $$
--
--   Identifiers are distinct with $O(\log(n+1))$ bits, messages have $O(\log(n+1))$ bits, and the algorithm needs no auxiliary graph structure, degree bound or knowledge of $n$.
--
--   This is the fractional solver of the paper in its general form: it covers open neighbourhoods (total domination), partial domination, forbidden candidates and red-blue domination.
--
--   **Formalization Note** One algorithm and one round count $T$ are chosen before the identifier exponent $k$ and the graph; only the message constant depends on $k$. The output is a rational per vertex.
--
--   Differences from the source:
--   - reading: broadcast CONGEST (each vertex receives its neighbours' messages) → the multiset of the neighbours' messages, without port numbers; reason: gives the algorithm less information, so the existence statement is at least as strong; a sender can prepend its O(log(n+1))-bit identifier
--   - reading: constant-round, identifiers and messages of O(log(n+1)) bits → ∃ algorithm ∃ T, ∀ k ∃ c: identifiers < (n+1)^k, messages ≤ c(⌊log₂ n⌋+1) bits; reason: the algorithm and its round count are independent of the identifier constant k; this is the stronger quantifier order
--   - encoding: for each edge rv both ends know whether v ∈ C(r); each demand knows whether r ∈ C(r); every vertex knows its demand bit and cost → local input covInput: demand bit, cost, self-cover bit, identifier sets of the incident covering pairs; reason: the broadcast model has no ports; identifiers of neighbours are learnable in one round, so no information is added
--   - encoding: costs c_v ∈ {1,…,b} for the candidates (admissible vertices) → costs in {1,…,b} at every vertex; reason: a vertex in no covering set covers nothing and its cost does not enter τ_c; the output is zero there, so the instances correspond one to one
--   - reading: a feasible fractional cover → x ≥ 0, x_v = 0 at every vertex in no C(r), and ∑_{v∈C(r)} x_v ≥ 1 for every demand; reason: §6.6 (p.42) says the output is a feasible vector on the admissible vertices; requiring it is at least as strong
-- source:
--   Amiri, Siebertz, Wawrzyniak, Paying for Fractional Error: Tight Constant-Round Approximation of Covering Problems with Short Broadcasts (arXiv:2611.02057, sha256 f4dc98d2cf73d74a105e5b0e61c4b72d15ae82b3f202490e2e4ecf864b40646a), §1.1, p.2 (PDF p.5), Theorem A; proof §6.6, pp.40–42 (PDF pp.43–45)

import Mathlib
import Definitions.Def_ShortBroadcastDom_closedNbhd
import Definitions.Def_ShortBroadcastDom_InClassC
import Definitions.Def_ShortBroadcastDom_BroadcastAlg
import Definitions.Def_ShortBroadcastDom_Supplement_tauRel
import Definitions.Def_ShortBroadcastDom_Supplement_covInput

namespace ShortBroadcastDom.Supplement

open ShortBroadcastDom

/-- **Theorem A (constant-round fractional solver for general covering relations).** Amiri,
Siebertz, Wawrzyniak, *Paying for Fractional Error* (arXiv:2611.02057, sha256 prefix f4dc98d2),
§1.1, p.2 (PDF 5): "For fixed rationals ρ ≥ 1 and δ > 0, and a fixed integer b ≥ 1, there is an
algorithm that computes a feasible fractional cover of cost at most (1 + δ)τc on every G ∈ Cρ in a
constant number of deterministic broadcast CONGEST rounds. The algorithm requires no auxiliary
graph structure, degree bound, or knowledge of the graph order." Setting (p.2): each demand `r` has
a nonempty set `C(r) ⊆ N[r]` of allowed candidates and the costs lie in `{1, …, b}`. Proved in
§6.6, pp.40–42.

**Formalization Note** For the fixed parameters there is one algorithm `alg` and one round count
`T`, chosen before the identifier exponent `k` and the graph; only the message constant `c` depends
on `k`. The local input is `covInput` (demand bit, cost, the incidence information of p.2) and the
output a rational `x_v`. The output is a feasible fractional cover: `x ≥ 0`, `x_v = 0` at every
vertex in no covering set (a vector on the admissible vertices, §6.6, p.41), and
`∑_{v ∈ C(r)} x_v ≥ 1` for every demand. Costs are given at every vertex; the cost of a vertex in no
covering set is irrelevant. -/
theorem theorem_A (ρ δ : ℚ) (hρ : 1 ≤ ρ) (hδ : 0 < δ) (b : ℕ) (hb : 1 ≤ b) :
    ∃ alg : BroadcastAlg CovInput ℚ, ∃ T : ℕ, ∀ k : ℕ, ∃ c : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (id : V → ℕ) (R : Finset V) (Cov : V → Finset V) (cost : V → ℕ),
        ValidIds k (Fintype.card V) id → InClassC (ρ : ℝ) G →
        (∀ r ∈ R, (Cov r).Nonempty ∧ Cov r ⊆ closedNbhd G r) →
        (∀ v, 1 ≤ cost v ∧ cost v ≤ b) →
          MsgBounded alg G id (covInput G id R Cov cost) T c (Fintype.card V) ∧
          (∀ v, 0 ≤ alg.realOut G id (covInput G id R Cov cost) T v) ∧
          (∀ v, (∀ r ∈ R, v ∉ Cov r) → alg.realOut G id (covInput G id R Cov cost) T v = 0) ∧
          (∀ r ∈ R, 1 ≤ ∑ v ∈ Cov r, alg.realOut G id (covInput G id R Cov cost) T v) ∧
          ∑ v, (cost v : ℝ) * alg.realOut G id (covInput G id R Cov cost) T v ≤
            (1 + (δ : ℝ)) * tauRel R Cov (fun v => (cost v : ℝ)) := by sorry

end ShortBroadcastDom.Supplement
