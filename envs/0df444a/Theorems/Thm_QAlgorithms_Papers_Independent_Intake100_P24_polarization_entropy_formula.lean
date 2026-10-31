-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P24_polarization_entropy_formula
-- name    : QAlgorithms.Papers.Independent.Intake100.P24.polarization_entropy_formula
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:18:33.365725+00:00
-- url     : https://prove2.me/theorems/a3d810c2-ad51-47b1-9e0c-eaba8b7ceea1
-- title:
--   Spectral entropy of an admissible polarization pair
-- statement:
--   Let $S$ be a positive semidefinite $2\times2$ Stokes matrix and $\alpha\in\mathbb C^2$ an unnormalized Jones vector such that $A=S-\alpha\alpha^\dagger\ge0$. Let $k_B>0$, use natural logarithms, and set $g(x)=(x+1)\log(x+1)-x\log x$, with $0\log0=0$. The RSF spectral entropy is
--
--   $$S[S;\alpha]=k_B\sum_{j=1}^2 g(\lambda_j(A))=k_B\operatorname{tr}\big((A+I)\log(A+I)-A\log A\big).$$
--
--   It is represented as an extended nonnegative value; this finite-mode sum is finite. The formula specializes (32) to an abstract admissible polarization pair without asserting that the raw multi-mode reductions (45),(47) produce one.
-- source:
--   Quantum features of macroscopic fields. Entropy and dynamics, arXiv:1904.06170v1, PDF p. 9, §VI.B, (56): admissible polarization entropy

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P24

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder Matrix.Norms.L2Operator

open MeasureTheory

open QAlgorithms.Papers.Independent.Dependency50.P49 (traceDual)

open QAlgorithms.Papers.Independent.Information100.P30 (IsPositiveMap)

namespace QAlgorithms.Papers.Independent.Intake100.P24

local instance : MeasurableSpace PolarizationMatrix := borel PolarizationMatrix

local instance : BorelSpace PolarizationMatrix := ⟨rfl⟩

/-- arXiv:1904.06170v1 PDF p.9, (56), using (32) on PDF p.5:
the spectral RSF entropy of an admissible polarization pair has the displayed
trace formula. Correction: the stray subscript 1 in the final logarithm of (56)
is omitted; both terms use A = S - |alpha><alpha|, as (32) and the definition
immediately below (56) require. This is not an assertion about the invalid
multi-q reduction (45),(47). Zero eigenvalues use 0 log 0 = 0. -/
theorem polarization_entropy_formula (kB : ℝ) (hkB : 0 < kB)
    (S : PolarizationMatrix) (alpha : JonesVector) (hS : S.PosSemidef)
    (hCov : (S - jonesOuter alpha).PosSemidef) :
    polarizationEntropy kB S alpha hCov =
      let A := S - jonesOuter alpha
      ENNReal.ofReal (kB *
        (((A + 1) * cfc Real.log (A + 1) - A * cfc Real.log A).trace.re)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P24

end
