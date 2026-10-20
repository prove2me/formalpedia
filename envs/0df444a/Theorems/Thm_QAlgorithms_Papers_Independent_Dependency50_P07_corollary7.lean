-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P07_corollary7
-- name    : QAlgorithms.Papers.Independent.Dependency50.P07.corollary7
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:29:02.517999+00:00
-- url     : https://prove2.me/theorems/dca0332d-a3da-4e17-88fe-a87da9dc9ce5
-- title:
--   Deterministic coarse graining controlling both conditional entropies
-- statement:
--   Fix a finite cq ensemble $XQ$ and a finite stochastic auxiliary $U\to X\to Q$. For every $\epsilon,\delta>0$, there is a positive threshold $N$ such that every integer $n\ge N$ admits a deterministic function $g:\mathcal X^n\to\mathcal U^n$ with
--
--   $$\frac1n H(Q^n|g(X^n))\le H(Q|U)+\delta,\qquad\left|\frac1n H(X^n|g(X^n))-H(X|U)\right|\le\delta.$$
--
--   The source is iid, and null fibers contribute zero to conditional entropy. The same map satisfies both bounds. This converts a stochastic auxiliary into a deterministic block coarse graining for the direct coding result.
-- source:
--   Distilling common randomness from bipartite quantum states, arXiv:quant-ph/0304196v2, PDF p. 10, Corollary 7: deterministic coarse graining with entropy control

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P07

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Information100.P04 (Measurement)

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Dependency50.P07

section CQStatements

variable {X Q Y T : Type} [Fintype X] [Fintype Q] [Fintype Y] [Fintype T]
  [DecidableEq X] [DecidableEq Q] [DecidableEq Y] [DecidableEq T]
  [Nonempty X] [Nonempty Q] [Nonempty Y] [Nonempty T]

/-- PDF pp.10--11, Corollary 7: one deterministic map satisfies both entropy bounds, with
absolute value in (19) and normalization only on the block entropies. -/
theorem corollary7 (E : CQData X Q) (hE : E.Valid) (V : Auxiliary X)
    (epsilon delta : ℝ) (he : 0 < epsilon) (hd : 0 < delta) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      ∃ g : (Fin n → X) → (Fin n → Fin V.size),
        quantumGivenCoarse E n g / n ≤ quantumGivenAux E V + delta ∧
        |classicalGivenCoarse E n g / n - classicalGivenAux E V| ≤ delta := by sorry

end CQStatements

end QAlgorithms.Papers.Independent.Dependency50.P07

end
