-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P29_haarEntryMoments
-- name    : QAlgorithms.Papers.Independent.Advance50.P29.haarEntryMoments
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:26:28.384283+00:00
-- url     : https://prove2.me/theorems/d8885452-7825-493e-a718-6d28fae32ffb
-- title:
--   Appendix B: two Haar unitary entry moments
-- statement:
--   Let $M\ge1$ be an integer, let $U$ be Haar-uniform on the entire unitary group $U(M)$, and fix a row $i$ and column $j$. The integrands below are integrable. For every distinct second column $k\ne j$,
--
--   $$
--   \mathbb E|U_{ij}|^4=\frac2{M^2+M},\qquad\mathbb E\bigl(|U_{ij}|^2|U_{ik}|^2\bigr)=\frac1{M^2+M}.
--   $$
--
--   The first identity holds also for $M=1$; the second has an instance only when $M\ge2$. These moments yield the normalized-projector formula.
-- source:
--   A random-coding based proof for the quantum coding theorem, arXiv:0712.2558v1, PDF p. 21, Appendix B: two Haar unitary entry moments

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P29

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P29

open QAlgorithms MeasureTheory Filter

open QAlgorithms.Papers.Independent.Information100.P22
  (densityPurification coherentInformation singleUseInformation mixed)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Dependency50.P48 (wordProbability)

open QAlgorithms.Papers.Independent.Bridge50.P43 (tensorDensity)

open scoped Matrix ComplexConjugate ComplexOrder Topology

attribute [local instance] Classical.propDecidable

variable {I J E L : Type} [Fintype I] [DecidableEq I]

variable [Fintype J] [DecidableEq J] [Fintype E] [DecidableEq E]

variable [Fintype L] [DecidableEq L]

/-- PDF p.21, Appendix B: fourth entry moment, and the mixed entry moment only for
DISTINCT columns. The scalar group therefore satisfies only the first formula. -/
theorem haarEntryMoments (M : ℕ) (hM : 0 < M) (i j : Fin M) :
    (Integrable (fun U : Matrix.unitaryGroup (Fin M) ℂ => Complex.normSq (U i j) ^ 2)
      (Schur.unitaryHaar M) ∧
    (∫ U : Matrix.unitaryGroup (Fin M) ℂ, Complex.normSq (U i j) ^ 2
      ∂(Schur.unitaryHaar M)) = 2 / ((M : ℝ) ^ 2 + M)) ∧
    ∀ k : Fin M, j ≠ k →
      Integrable (fun U : Matrix.unitaryGroup (Fin M) ℂ =>
        Complex.normSq (U i j) * Complex.normSq (U i k)) (Schur.unitaryHaar M) ∧
      (∫ U : Matrix.unitaryGroup (Fin M) ℂ,
        Complex.normSq (U i j) * Complex.normSq (U i k) ∂(Schur.unitaryHaar M)) =
          1 / ((M : ℝ) ^ 2 + M) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P29

end
