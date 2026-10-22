-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P22_formation_andSeparableDistance
-- name    : QAlgorithms.Papers.Independent.Gap48.P22.formation_andSeparableDistance
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:15:50.079599+00:00
-- url     : https://prove2.me/theorems/b8dc5463-e0b7-4298-87b7-0b1f5ba4920d
-- title:
--   Entanglement of formation and separable-state distance
-- statement:
--   Let $\rho^{AB}$ be a density operator on finite positive-dimensional systems, and put $d=\min\{\dim A,\dim B\}$. Write $E_F(\rho)$ for the minimum average marginal entropy over pure-state decompositions of $\rho$, with unit vectors and probability weights. All entropies and logarithms below use base two, and $h_2$ is binary entropy with $0\log0=0$.
--
--   For every $\delta\ge0$ and separable density operator $\sigma$ satisfying $\tfrac12\|\rho-\sigma\|_1\le\delta$,
--
--   $$E_F(\rho)\le\sqrt\delta\log_2d+(1+\sqrt\delta)h_2\!\left(\frac{\sqrt\delta}{1+\sqrt\delta}\right).$$
--
--   Conversely, for every $\varepsilon\ge0$ with $E_F(\rho)\le\varepsilon$, some separable density operator $\sigma$ satisfies
--
--   $$\tfrac12\|\rho-\sigma\|_1\le\sqrt{\ln2}\sqrt\varepsilon.$$
--
--   Together these statements quantify the two directions relating formation entanglement to distance from separable states. The first direction includes every nonnegative $\delta$, without imposing an upper bound of one.
-- source:
--   Squashed entanglement, k-extendibility, quantum Markov chains, and recovery maps, arXiv:1410.4184v4, PDF p. 4, Proposition 1 / Eq.(9)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P22

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Gap48.P22

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P12 (squashedEntanglement KExtendible)

open QAlgorithms.Papers.Independent.Claimed50.P33
  (RegisterBasis registerMarginal entropyAt conditionalMultipartiteInformation singleParties
   forgetEnvironment)

open QAlgorithms.Papers.Independent.Renew46.P35 (classicalCMI)

open QAlgorithms.Entanglement (IsSeparableDensity)

/-- Proposition 1, PDF pp.4–5, Eq.(9): both directions, half trace distance;
all occurrences of delta in the first bound are under a square root. -/
theorem formation_andSeparableDistance {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho) :
    (∀ delta : ℝ, 0 ≤ delta → ∀ sigma : Matrix (A × B) (A × B) ℂ,
      IsSeparableDensity sigma → traceDistance rho sigma ≤ delta →
      formationEntanglement rho ≤ Real.sqrt delta *
        Real.logb 2 (min (Fintype.card A) (Fintype.card B) : ℕ) +
        (1+Real.sqrt delta) * binEntropy2 (Real.sqrt delta / (1+Real.sqrt delta))) ∧
    (∀ epsilon : ℝ, 0 ≤ epsilon → formationEntanglement rho ≤ epsilon →
      ∃ sigma : Matrix (A × B) (A × B) ℂ, IsDensityMatrix sigma ∧ IsSeparableDensity sigma ∧
        traceDistance rho sigma ≤ Real.sqrt (Real.log 2) * Real.sqrt epsilon) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P22

end
