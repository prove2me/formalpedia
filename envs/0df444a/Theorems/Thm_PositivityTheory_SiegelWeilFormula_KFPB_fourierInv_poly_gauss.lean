-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFPB_fourierInv_poly_gauss
-- name    : PositivityTheory.SiegelWeilFormula.KFPB.fourierInv_poly_gauss
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:17:32.803894+00:00
-- url     : https://prove2.me/theorems/d09825a8-5949-41f9-a628-e70c24f6fb63
-- title:
--   KFPB: fourier Inv poly gauss
-- statement:
--   The KFPB construction uses the fourier Inv poly gauss property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/PolynomialGaussianIntegrals/IntegrablePolyGauss.lean#L182-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/PolynomialGaussianIntegrals/IntegrablePolyGauss.lean#L182-L208

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LocalOperatorBlocks_IntgPowQuad
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_PolynomialGaussianIntegrals_IntegrablePolyGauss
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KLI_J_eq
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KLI_J_zero
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KLI_intg_pow_quad
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KLI_pk_deg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped FourierTransform
open MeasureTheory Complex MvPolynomial
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KFPB
open PositivityTheory.SiegelWeilFormula.KLI (J pk J_eq J_zero intg_pow_quad pk_deg)
variable {ι : Type} [Fintype ι]

theorem PositivityTheory.SiegelWeilFormula.KFPB.fourierInv_poly_gauss {ι : Type} [Fintype ι] (b : ℝ) (hb : 0 < b) (Q : MvPolynomial ι ℂ) :
    ∃ Q' : MvPolynomial ι ℂ, Q'.totalDegree ≤ Q.totalDegree ∧ ∀ u : EuclideanSpace ℝ ι,
      𝓕⁻ (fun η : EuclideanSpace ℝ ι =>
          MvPolynomial.eval (fun i => ((η i : ℝ) : ℂ)) Q * (Real.exp (-(b * ‖η‖ ^ 2)) : ℂ)) u =
        MvPolynomial.eval (fun i => ((u i : ℝ) : ℂ)) Q' * (Real.exp (-(Real.pi ^ 2 / b * ‖u‖ ^ 2)) : ℂ) := by sorry
