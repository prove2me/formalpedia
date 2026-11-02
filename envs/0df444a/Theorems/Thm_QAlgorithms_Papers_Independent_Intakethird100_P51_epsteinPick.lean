-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P51_epsteinPick
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P51.epsteinPick
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:06:17.226692+00:00
-- url     : https://prove2.me/theorems/df88c2e7-c510-43cc-b1b1-0e11581b0180
-- title:
--   Appendix A: Epstein trace function maps upper half-plane to itself
-- statement:
--   Let $A>0$ and let $K,B$ be self-adjoint matrices on a nonzero finite complex system. For $\operatorname{Im}z>0$, define
--   $$g(z)=\operatorname{Tr}\exp\bigl(K+\operatorname{Log}(zA+B)\bigr),$$
--   where $\operatorname{Log}$ is the principal holomorphic matrix logarithm obtained by the contour-resolvent formula. Then $g$ is analytic on the upper half-plane and
--   $$\operatorname{Im}g(z)>0\qquad(\operatorname{Im}z>0).$$
--   An admissible positively oriented contour exists for each pencil value. This is Epstein’s Pick-function step; $B$ need not be positive.
-- source:
--   Inequalities for Quantum Entropy: A Review with Conditions for Equality, arXiv:quant-ph/0205064v2, PDF p. 24, Appendix A: Epstein trace function maps upper half-plane to itself

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P51

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Intakethird100.P51

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact interfaces from the frozen accepted library; no local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy holevo IsLaw)

open QAlgorithms.Papers.Independent.Information100.P27 (average)

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy marginalAB channelAdjoint)

open QAlgorithms.Papers.Independent.Dependency50.P35 (marginalAC)

open QAlgorithms.Papers.Independent.Gap48.P19 (shannonNats)

open QAlgorithms.Papers.Independent.Gap48.P33 (measurementInformation)

section Statements

variable {A B C D J K O : Type}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype J] [Fintype K] [Fintype O]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

variable [DecidableEq J] [DecidableEq K] [DecidableEq O]

/-- Appendix A, equations (62)–(63), PDF p.24: Epstein's analytic Pick function.
The nonnormal pencil uses the principal contour logarithm, not Hermitian cfc. -/
theorem epsteinPick [Nonempty A] (R K B : Mat A) (hR : R.PosDef) (hK : K.IsHermitian) (hB : B.IsHermitian) :
    AnalyticOnNhd ℂ (epsteinTrace K R B) {z : ℂ | 0 < z.im} ∧
      ∀ z : ℂ, 0 < z.im →
        (∃ cr : ℂ × ℝ, UpperLogContour (z • R + B) cr.1 cr.2) ∧
        0 < (epsteinTrace K R B z).im := by sorry

end Statements

end QAlgorithms.Papers.Independent.Intakethird100.P51

end
