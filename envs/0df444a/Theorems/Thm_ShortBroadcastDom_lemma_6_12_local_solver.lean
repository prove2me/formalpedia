-- Prove2me | Theorems.Thm_ShortBroadcastDom_lemma_6_12_local_solver
-- name    : ShortBroadcastDom.lemma_6_12_local_solver
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:27:05.536203+00:00
-- url     : https://prove2.me/theorems/d3c47f3b-b740-4654-ae14-2b4ca938fcfd
-- title:
--   Lemma 6.12 — a constant-round $(1+\xi)$-solver for local tasks of bounded diameter and optimum
-- statement:
--   Fix $a\ge1$, integers $B_0$ and $D$, a real $K_0$ and a positive rational $\xi$. There is a deterministic broadcast CONGEST algorithm, with a round count $T$ and a common denominator $Q\ge1$ depending only on these parameters, with the following property. Let $H$ be a connected finite graph of diameter at most $D$ whose subgraphs all have density at most $a$; every vertex knows whether it is a demand (the demand set $R$) and its integer cost $1\le c_v\le B_0$. If $\tau_{R,c}(H)\le K_0$, the algorithm outputs rationals $x_v$ with $Qx_v\in\mathbb Z$ such that
--
--   $$
--   x\ge0,\qquad \sum_{v\in N_H[r]}x_v\ge1\ (r\in R),\qquad \sum_v c_vx_v\le(1+\xi)\,\tau_{R,c}(H).
--   $$
--
--   Identifiers and messages have $O(\log(N+1))$ bits for any ambient order $N\ge|V(H)|$. This solves the local tasks of the fractional solver (Theorem 6.13).
--
--   Differences from the source:
--   - generalization: identifiers and messages of O(log(n+1)) bits, n = |V(H)| → identifiers < (N+1)^k and messages ≤ c(⌊log₂ N⌋+1) bits for any ambient N ≥ |V(H)|; reason: N = |V(H)| is the paper's case; the proof of Theorem 6.13 runs the solver on subgraphs with the ambient identifiers (p.36: "Counts are at most a fixed multiple of the ambient graph order")
--   - reading: broadcast CONGEST, round bound and denominator depending only on the fixed parameters → multiset reception; ∃ algorithm ∃ T ∃ Q, ∀ k ∃ c; reason: as in Theorem 6.1: less information for the algorithm, and the algorithm is independent of the identifier constant
--   - encoding: H has diameter at most D → H connected and dist(u, v) ≤ D for all u, v; reason: the same condition
-- source:
--   Amiri, Siebertz, Wawrzyniak, Paying for Fractional Error: Tight Constant-Round Approximation of Covering Problems with Short Broadcasts (arXiv:2611.02057, sha256 f4dc98d2cf73d74a105e5b0e61c4b72d15ae82b3f202490e2e4ecf864b40646a), §6.4.1, p.35 (PDF p.38), Lemma 6.12

import Mathlib
import Definitions.Def_ShortBroadcastDom_SubgraphDensityLE
import Definitions.Def_ShortBroadcastDom_tauOn
import Definitions.Def_ShortBroadcastDom_BroadcastAlg

namespace ShortBroadcastDom

/-- **Lemma 6.12 (the local task solver).** Amiri, Siebertz, Wawrzyniak, *Paying for Fractional Error* (arXiv:2611.02057, sha256 prefix
f4dc98d2), §6.4.1, p.35 (PDF 38): "Fix a ≥ 1, B0, K0, D and
a positive rational ξ. Assume that H is connected, has diameter at most D, and satisfies the
subgraph-density bound a, that R ⊆ V(H) is known by local membership bits, and that locally known
integer costs satisfy 1 ≤ cv ≤ B0. If τR,c(H) ≤ K0, a deterministic broadcast CONGEST algorithm
returns a feasible vector of cost at most (1 + ξ)τR,c(H). Its round bound and a common denominator
for all coordinates depend only on the fixed parameters."

**Formalization Note** The local input is `(demand bit, integer cost)`, the output a rational
`x_v`. The algorithm, its round count `T` and the common denominator `Q ≥ 1` are chosen from the
fixed parameters only. Identifiers and messages are bounded in terms of an ambient order
`N ≥ |V(H)|` (identifiers `< (N+1)^k`, messages `≤ c(⌊log₂ N⌋ + 1)` bits); `N = |V(H)|` is the
paper's case, and the general `N` is how the proof of Theorem 6.13 runs this solver on subgraphs
(p.36: "Counts are at most a fixed multiple of the ambient graph order"). -/
theorem lemma_6_12_local_solver (a : ℝ) (ha : 1 ≤ a) (B0 : ℕ) (K0 : ℝ) (Dm : ℕ) (ξ : ℚ) (hξ : 0 < ξ) :
    ∃ alg : BroadcastAlg (Bool × ℕ) ℚ, ∃ T Q : ℕ, 0 < Q ∧ ∀ k : ℕ, ∃ c : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
        (N : ℕ) (id : V → ℕ) (inp : V → Bool × ℕ),
        Fintype.card V ≤ N → ValidIds k N id → H.Connected → (∀ u v, H.dist u v ≤ Dm) →
        SubgraphDensityLE a H → (∀ v, 1 ≤ (inp v).2 ∧ (inp v).2 ≤ B0) →
        tau H (demandsOf inp) (costsOf inp) ≤ K0 →
          MsgBounded alg H id inp T c N ∧
          (∀ v, 0 ≤ alg.realOut H id inp T v) ∧
          (∀ r ∈ demandsOf inp, 1 ≤ ∑ v ∈ closedNbhd H r, alg.realOut H id inp T v) ∧
          ∑ v, costsOf inp v * alg.realOut H id inp T v ≤
            (1 + (ξ : ℝ)) * tau H (demandsOf inp) (costsOf inp) ∧
          ∀ v, ∃ z : ℤ, (Q : ℚ) * alg.output H id inp T v = z := by sorry

end ShortBroadcastDom
