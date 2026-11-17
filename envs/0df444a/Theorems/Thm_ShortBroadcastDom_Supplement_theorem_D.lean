-- Prove2me | Theorems.Thm_ShortBroadcastDom_Supplement_theorem_D
-- name    : ShortBroadcastDom.Supplement.theorem_D
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T23:44:00.916627+00:00
-- url     : https://prove2.me/theorems/a7e54a89-fd41-4eb1-86a4-42bf3cd1c1a4
-- title:
--   Theorem D — randomized constant-round and deterministic $O(\log^*n)$-round $(1+\varepsilon)$-approximate integral covers on $\mathcal C_\rho$
-- statement:
--   Fix a rational $\rho\ge1$, an integer $b\ge1$ and $\varepsilon>0$. Consider general covering instances on $G\in\mathcal C_\rho$: demands $R$, nonempty covering sets $C(r)\subseteq N_G[r]$ and costs $c_v\in\{1,\dots,b\}$, with $\mathrm{OPT}_c$ the minimum cost of an integral cover.
--
--   1. There is a randomized broadcast CONGEST algorithm with a constant number of rounds whose output $D$ is a cover ($D\cap C(r)\ne\emptyset$ for every demand) for every outcome of the random bits, and whose expected cost satisfies
--   $$\mathbb E\Bigl[\sum_{v\in D}c_v\Bigr]\le(1+\varepsilon)\,\mathrm{OPT}_c .$$
--   2. If the vertices know a common polynomial bound on the identifiers, there is a deterministic broadcast CONGEST algorithm that returns a cover of cost at most $(1+\varepsilon)\mathrm{OPT}_c$ in $O(\log^*n)$ rounds.
--
--   The constants in the round bounds depend only on $\rho,b,\varepsilon$.
--
--   **Formalization Note** (i) Each vertex receives a fixed number $\beta$ of independent fair bits, chosen with the algorithm; the expectation is the exact average over all $2^{\beta n}$ outcomes, and feasibility and the message bound hold for every outcome. (ii) Each vertex receives a common number $M$ with every identifier below $M\le(n+1)^k$; the algorithm stops after $T(M)$ rounds for a function $T$ fixed with the algorithm, and $T(M)\le K(\log^*n+1)$. As for the message constant, $K$ may depend on the degree $k$ of the polynomial bound. $\log^*$ is the published base-2 iterated logarithm.
--
--   Differences from the source:
--   - reading: broadcast CONGEST (each vertex receives its neighbours' messages) → the multiset of the neighbours' messages, without port numbers; reason: gives the algorithm less information, so the existence statement is at least as strong; a sender can prepend its O(log(n+1))-bit identifier
--   - reading: constant-round, identifiers and messages of O(log(n+1)) bits → ∃ algorithm ∃ T, ∀ k ∃ c: identifiers < (n+1)^k, messages ≤ c(⌊log₂ n⌋+1) bits; reason: the algorithm and its round count are independent of the identifier constant k; this is the stronger quantifier order
--   - encoding: for each edge rv both ends know whether v ∈ C(r); each demand knows whether r ∈ C(r); every vertex knows its demand bit and cost → local input covInput: demand bit, cost, self-cover bit, identifier sets of the incident covering pairs; reason: the broadcast model has no ports; identifiers of neighbours are learnable in one round, so no information is added
--   - reading: a randomized algorithm; always feasible; expected cost → β fair bits per vertex with β fixed before the graph; feasibility and message bound for every outcome; expectation as the exact average over all outcomes; reason: the randomized scheme draws a bounded number of fair bits per vertex (Lemma 6.9, §8); a fixed β is at least as strong as an unrestricted source
--   - reading: vertices know a common polynomial bound on the identifiers; O(log* n) rounds with constants depending only on ρ, b, ε → input M with id < M ≤ (n+1)^k; rounds T(M) ≤ K(log* n + 1), K fixed before the graph and allowed to depend on k; reason: the degree k of the polynomial bound is a fixed constant of the convention (like the message constant); log*((n+1)^k) − log* n depends on k
--   - encoding: log* n → the least k such that k iterations of ⌊log₂⌋ send n to at most 1; reason: fixes the integer convention used for the round-count function; replacing the usual real iteration changes log* only by an absolute constant
-- source:
--   Amiri, Siebertz, Wawrzyniak, Paying for Fractional Error: Tight Constant-Round Approximation of Covering Problems with Short Broadcasts (arXiv:2611.02057, sha256 f4dc98d2cf73d74a105e5b0e61c4b72d15ae82b3f202490e2e4ecf864b40646a), §1.3, p.4 (PDF p.7), Theorem D; proof §8, pp.48–50 (PDF pp.51–53)

import Mathlib
import Definitions.Def_ShortBroadcastDom_closedNbhd
import Definitions.Def_ShortBroadcastDom_InClassC
import Definitions.Def_ShortBroadcastDom_BroadcastAlg
import Definitions.Def_ShortBroadcastDom_Supplement_tauRel
import Definitions.Def_ShortBroadcastDom_Supplement_covInput
import Definitions.Def_ShortBroadcastDom_Supplement_logStar

namespace ShortBroadcastDom.Supplement

open ShortBroadcastDom

/-- **Theorem D (integral approximation schemes for general covering).** Amiri, Siebertz,
Wawrzyniak, *Paying for Fractional Error* (arXiv:2611.02057, sha256 prefix f4dc98d2), §1.3, p.4
(PDF 7): "For fixed rational ρ ≥ 1, integer b ≥ 1, and ε > 0, the following guarantees hold on
every G ∈ Cρ: (i) There exists a randomized algorithm that computes an integral cover that is always
feasible and has expected cost at most (1 + ε) OPTc in a constant number of broadcast CONGEST
rounds. (ii) If vertices know a common polynomial bound on the identifiers, there exists a
deterministic algorithm that computes a feasible integral cover of cost at most (1 + ε) OPTc in
O(log∗n) broadcast CONGEST rounds. The constants in the round bounds depend only on ρ, b, ε."
Setting of §1.1, p.2 (general covering relations `C(r) ⊆ N[r]`, costs in `{1, …, b}`); proof §8.

**Formalization Note** Two conjuncts.
(i) Randomness: every vertex receives, besides its covering input, `β` independent fair bits
`ω_v : Fin β → Bool`, with `β` fixed together with the algorithm and its round count `T` (Lemma 6.9
uses a fixed number of fair bits per vertex). "Always feasible" holds for every outcome
`ω : V → Fin β → Bool`, as does the message bound; the expected cost is the exact average
`2^{-β n} ∑_ω cost(D_ω)` over all outcomes.
(ii) Every vertex also receives a common number `M` with `id v < M ≤ (n + 1)^k` (a polynomial bound
on the identifiers known to all). The algorithm stops after `T(M)` rounds for a function `T` fixed
with the algorithm, so all vertices stop together, and `T(M) ≤ K (log* n + 1)` with `K` fixed
before the graph; `K` may depend on the degree `k` of the polynomial bound, like the message
constant. `log*` is `Supplement.logStar`, the least number of iterations of `Nat.log 2` needed to
reach a value at most one.
`OPT_c` is the integral optimum `optRel`; the output is the set of vertices outputting `true`. -/
theorem theorem_D (ρ : ℚ) (hρ : 1 ≤ ρ) (b : ℕ) (hb : 1 ≤ b) (ε : ℝ) (hε : 0 < ε) :
    (∃ β : ℕ, ∃ alg : BroadcastAlg (CovInput × (Fin β → Bool)) Bool, ∃ T : ℕ, ∀ k : ℕ, ∃ c : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (id : V → ℕ) (R : Finset V) (Cov : V → Finset V) (cost : V → ℕ),
        ValidIds k (Fintype.card V) id → InClassC (ρ : ℝ) G →
        (∀ r ∈ R, (Cov r).Nonempty ∧ Cov r ⊆ closedNbhd G r) →
        (∀ v, 1 ≤ cost v ∧ cost v ≤ b) →
          (∀ ω : V → Fin β → Bool,
            MsgBounded alg G id (fun v => (covInput G id R Cov cost v, ω v)) T c
              (Fintype.card V) ∧
            ∀ r ∈ R, ∃ v ∈ alg.outSet G id (fun v => (covInput G id R Cov cost v, ω v)) T,
              v ∈ Cov r) ∧
          (∑ ω : V → Fin β → Bool,
              ∑ v ∈ alg.outSet G id (fun v => (covInput G id R Cov cost v, ω v)) T,
                (cost v : ℝ)) / (2 : ℝ) ^ (β * Fintype.card V) ≤
            (1 + ε) * optRel R Cov (fun v => (cost v : ℝ))) ∧
    (∃ alg : BroadcastAlg (CovInput × ℕ) Bool, ∃ T : ℕ → ℕ, ∀ k : ℕ, ∃ K c : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (id : V → ℕ) (R : Finset V) (Cov : V → Finset V) (cost : V → ℕ) (M : ℕ),
        ValidIds k (Fintype.card V) id → (∀ v, id v < M) → M ≤ (Fintype.card V + 1) ^ k →
        InClassC (ρ : ℝ) G →
        (∀ r ∈ R, (Cov r).Nonempty ∧ Cov r ⊆ closedNbhd G r) →
        (∀ v, 1 ≤ cost v ∧ cost v ≤ b) →
          T M ≤ K * (logStar (Fintype.card V) + 1) ∧
          MsgBounded alg G id (fun v => (covInput G id R Cov cost v, M)) (T M) c
            (Fintype.card V) ∧
          (∀ r ∈ R, ∃ v ∈ alg.outSet G id (fun v => (covInput G id R Cov cost v, M)) (T M),
            v ∈ Cov r) ∧
          ∑ v ∈ alg.outSet G id (fun v => (covInput G id R Cov cost v, M)) (T M), (cost v : ℝ) ≤
            (1 + ε) * optRel R Cov (fun v => (cost v : ℝ))) := by sorry

end ShortBroadcastDom.Supplement
