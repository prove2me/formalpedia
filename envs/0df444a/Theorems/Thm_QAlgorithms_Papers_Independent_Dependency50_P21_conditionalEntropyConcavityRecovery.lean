-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P21_conditionalEntropyConcavityRecovery
-- name    : QAlgorithms.Papers.Independent.Dependency50.P21.conditionalEntropyConcavityRecovery
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:13:36.716415+00:00
-- url     : https://prove2.me/theorems/22e99fe1-b41b-4db3-9284-271b39eb062c
-- title:
--   Universal recovery refinement of conditional entropy concavity
-- statement:
--   Fix a density operator ρAB on finite-dimensional complex systems A,B. Define R:B→AB from ρAB and trA by the averaged rotated Petz construction (21), independently of any ensemble decomposition. For every finite label set X, probability vector ν on X, and density operators ρˣAB satisfying ρAB=∑xν(x)ρˣAB, one has
--
--   $$H(A\mid B)_\rho-\sum_{x\in X}\nu(x)H(A\mid B)_{\rho^x}\ge -2\log\!\left(\sum_{x\in X}\nu(x)F\bigl(\rho^x_{AB},\mathcal R(\rho^x_B)\bigr)\right).$$
--
--   Conditional entropy uses natural logarithms and F is root fidelity; zero weights are allowed. This supplies one explicit recovery map for all decompositions of the fixed state.
--
--   **Source correction.** The map uses the t/2 average of (21), as in the cited Remark 2.2, instead of the t average printed after (102).
-- source:
--   Universal recovery maps and approximate sufficiency of quantum relative entropy, arXiv:1509.07127v3, PDF p. 17, Corollary 4.2

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P21

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Matrix.Norms.L2Operator

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Dependency50.P21

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the named interfaces from the pinned accepted paper library.

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P67 (conditionalEntropy)

/-- Corollary 4.2, PDF p.17, Eq.(102). SOURCE CORRECTION: the explicit map uses
Eq.(21)'s R^(t/2) average rather than the printed R^t. It is fixed from rhoAB before
all ensemble decompositions. Weights may vanish. The accepted conditional entropy
is in bits, so multiplication by log(2) converts it to the source's nats. -/
theorem conditionalEntropyConcavityRecovery {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (rho : Mat (I × J)) (hrho : IsDensityMatrix rho) :
    ∀ {X : Type*} [Fintype X] (nu : X → ℝ) (states : X → Mat (I × J)),
      (∀ x, 0 ≤ nu x) → (∑ x, nu x) = 1 → (∀ x, IsDensityMatrix (states x)) →
      rho = ∑ x, (nu x : ℂ) • states x →
      fidelityPenalty (∑ x, nu x * rootFidelity (states x)
        (recovery rho (traceLeft (α := I) (β := J)) (traceLeft (states x)))) ≤
        ((Real.log 2 * conditionalEntropy rho -
          ∑ x, nu x * (Real.log 2 * conditionalEntropy (states x)) : ℝ) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P21

end
