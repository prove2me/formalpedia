-- Prove2me | Theorems.Thm_RankCutFacility_Shifted_Supplement_full_space_lower_bound
-- name    : RankCutFacility.Shifted.Supplement.full_space_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:24:38.012741+00:00
-- url     : https://prove2.me/theorems/6d3aff95-8062-4dc4-adfc-6103a5326bd8
-- title:
--   Corollary 6.7 — $3N/(N+3)$ lower bound in the full-space nonuniform model
-- statement:
--   Use the metric $X\cup Y$ of Lemma 6.2 with every point a feasible facility and opening costs $f_{y_I}=1$, $f_{x_i}=1+N/3$.
--
--   **Corollary 6.7.** For every integer $N\ge2$ this is a finite metric space in which every point is a feasible facility, the costs are positive and nonuniform, and for every randomized online algorithm there is a demand-point multiset of size $N$ (inside $X$) with
--
--   $$\frac{\mathbb E[\mathrm{ALG}]}{\mathrm{OPT}}\ge\frac{3N}{N+3}$$
--
--   under uniformly random order. Consequently the asymptotic random-order competitive ratio of full-space facility location with nonuniform opening costs is at least $3$: for every $c<3$ and every $N_0$ there is $N\ge N_0$ such that every randomized online algorithm on this finite full-space instance has a demand multiset of size $N$ with $\mathbb E[\mathrm{ALG}]>c\cdot\mathrm{OPT}$.
--
--   This is part (b) of Theorem 1.3 and the lower half of the uniform/nonuniform separation.
--
--   Differences from the source:
--   - generalization: for every algorithm there is a finite full-space metric with nonuniform costs and a multiset → one explicit metric and cost function, fixed by N before the algorithm, and a multiset of points of X; reason: the explicit instance is the one the source's proof uses; it witnesses the existential claim for every algorithm
--   - encoding: the asymptotic random-order competitive ratio is at least 3 → for every c < 3 and every N₀ there is N ≥ N₀ such that every randomized algorithm on the size-N full-space instance has a multiset with E[ALG] > c · OPT; reason: this is the statement that no algorithm family achieves any ratio below 3 asymptotically
--   - encoding: E[ALG]/OPT ≥ r → E[ALG] ≥ r · OPT; reason: OPT > 0 on these instances, so the two are equivalent
--   - encoding: a randomized online algorithm (knowing the metric, costs, horizon and demand distribution, possibly opening several facilities per round) → a probability mass function over deterministic online algorithms, each a map from the revealed request prefix to the finite set of candidates opened in that round, independent of the demand randomness; reason: on a fixed finite instance with fixed horizon only finitely many deterministic behaviours exist, so every randomized algorithm is such a mixture; the public data are fixed before the algorithm is chosen
--   - encoding: real costs with d(x, ∅) = +∞ → costs in [0, ∞] (ENNReal), with d(x, ∅) = ⊤; reason: an algorithm that leaves the open set empty in some round pays +∞, exactly as in the source
--   - encoding: expectation over the uniformly random arrival order → finite average over all n! permutations of the labeled copies; reason: this is exactly the finite uniform law; no measurability assumption is needed
-- source:
--   Jianhao Jia, Bo Peng, Zhihao Gavin Tang, STOC 2027 submission #388 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/388.pdf, Theorem 1.3(b) (printed p. 2, PDF p. 4) and Corollary 6.7 (printed p. 21, PDF p. 23)

import Definitions.Def_RankCutFacility_Shifted_Supplement_Online

noncomputable section
open scoped ENNReal

namespace RankCutFacility.Shifted.Supplement

/-- Theorem 1.3(b) / Corollary 6.7 (PDF pp. 4, 23; printed pp. 2, 21). For every `N ≥ 2`, the
finite metric `X ∪ Y` with every point a feasible facility and the nonuniform costs
`f_{y_I} = 1`, `f_{x_i} = 1 + N/3` (fixed before the algorithm) defeats every randomized online
algorithm with ratio `3N/(N+3)` on some demand multiset of size `N`. Consequently, for every
`c < 3` and arbitrarily large `N`, every randomized algorithm for such a finite full-space
nonuniform-cost instance has a demand multiset with `E[ALG] > c · OPT`. -/
theorem full_space_lower_bound :
    (∀ N : ℕ, 2 ≤ N →
      (∀ a b : LBPoint N, lbDist N a b = 0 ↔ a = b) ∧
      (∀ a b : LBPoint N, lbDist N a b = lbDist N b a) ∧
      (∀ a b c : LBPoint N, lbDist N a c ≤ lbDist N a b + lbDist N b c) ∧
      (∀ p : LBPoint N, 0 < lbFullFee N p) ∧
      ∀ ρ : PMF (OnlineAlg (LBPoint N) (LBPoint N)), ∃ w : Fin N → Fin (lbM N),
        ENNReal.ofReal (3 * (N : ℝ) / ((N : ℝ) + 3) *
            offlineOpt (lbDist N) id (lbFullFee N) (fun i => (Sum.inl (w i) : LBPoint N))) ≤
          randExpected (lbDist N) id (lbFullFee N) ρ (fun i => (Sum.inl (w i) : LBPoint N))) ∧
    (∀ c : ℝ, c < 3 → ∀ N₀ : ℕ, ∃ N : ℕ, N₀ ≤ N ∧ 2 ≤ N ∧
      ∀ ρ : PMF (OnlineAlg (LBPoint N) (LBPoint N)), ∃ w : Fin N → Fin (lbM N),
        ENNReal.ofReal (c *
            offlineOpt (lbDist N) id (lbFullFee N) (fun i => (Sum.inl (w i) : LBPoint N))) <
          randExpected (lbDist N) id (lbFullFee N) ρ (fun i => (Sum.inl (w i) : LBPoint N))) := by sorry

end RankCutFacility.Shifted.Supplement
