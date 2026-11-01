-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P45_conditionalRateShifts
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P45.conditionalRateShifts
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:13:12.812191+00:00
-- url     : https://prove2.me/theorems/3817399e-8ed8-4d90-ba19-3374482b4428
-- title:
--   §5.2, conditional rate shifts (43)
-- statement:
--   For nonorthogonal finite laws and a null-admissible nonrandomized test sequence, original error-rate limits exist exactly when the corresponding conditional limits exist. Their values satisfy
--
--   $$\alpha_R=-\log\psi_0+\widetilde\alpha_R,\qquad\beta_R=-\log\psi_1+\widetilde\beta_R.$$
--
--   Both $\psi_0,\psi_1$ are positive. The shifts are finite and apply also to infinite rate limits.
-- source:
--   Asymptotic Error Rates in Quantum Hypothesis Testing, arXiv:0708.4282v1, PDF p. 23, §5.2, conditional rate shifts (43)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P45

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P45

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder ENNReal BigOperators Topology

open QAlgorithms.Papers.Independent.Information100.P07
  (support positivePart positiveProjection IsProjection)

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Dependency50.P28 (logNonnegativeExtended relativeEntropy)

open QAlgorithms.Papers.Independent.Claimed50.P15 (positiveMatrixRpow)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- arXiv:0708.4282v1, PDF p.23: §5.2, conditional rate shifts (43). -/
theorem conditionalRateShifts (p q : I → ℝ) (hp : IsLaw p) (hq : IsLaw q)
    (h0 : 0 < overlapMass p q) (h1 : 0 < overlapMass q p)
    (f : (k : ℕ) → ObservableWords p q (k+1) → Bool)
    (hf : ∀ k, NullAdmissible p q (f k)) :
    (∀ a : EReal,
      HasRate (fun k => restrictedAlpha p q (f k)) a ↔
      HasRate (fun k => observableAlpha p q (f k))
        (((-Real.log (overlapMass p q) : ℝ) : EReal)+a)) ∧
    (∀ b : EReal,
      HasRate (fun k => restrictedBeta p q (f k)) b ↔
      HasRate (fun k => observableBeta p q (f k))
        (((-Real.log (overlapMass q p) : ℝ) : EReal)+b)) ∧
    ((∃ a, HasRate (fun k => observableAlpha p q (f k)) a) ↔
     (∃ a, HasRate (fun k => restrictedAlpha p q (f k)) a)) ∧
    ((∃ b, HasRate (fun k => observableBeta p q (f k)) b) ↔
     (∃ b, HasRate (fun k => restrictedBeta p q (f k)) b)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P45

end
