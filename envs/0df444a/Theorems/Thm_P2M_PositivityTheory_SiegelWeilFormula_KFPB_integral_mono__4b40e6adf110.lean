-- Prove2me | Theorems.Thm_P2M_PositivityTheory_SiegelWeilFormula_KFPB_integral_mono__4b40e6adf110
-- name    : P2M_PositivityTheory_SiegelWeilFormula_KFPB_integral_mono__4b40e6adf110
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:17:56.027893+00:00
-- url     : https://prove2.me/theorems/2d66c4c8-214b-4c37-94f5-b38b047033dc
-- title:
--   P2 M Positivity Theory Siegel Weil Formula KFPB integral mono  4b40e6adf110: P2 M Positivity Theory Siegel Weil Formula KFPB integral mono  4b40e6adf110
-- statement:
--   The P2 M Positivity Theory Siegel Weil Formula KFPB integral mono  4b40e6adf110 construction uses the P2 M Positivity Theory Siegel Weil Formula KFPB integral mono  4b40e6adf110 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/PolynomialGaussianIntegrals/IntegrablePolyGauss.lean#L143-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/PolynomialGaussianIntegrals/IntegrablePolyGauss.lean#L143-L148

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

theorem P2M_PositivityTheory_SiegelWeilFormula_KFPB_integral_mono__4b40e6adf110 {b : ℝ} (hb : 0 < b) (s : ι →₀ ℕ) (u : EuclideanSpace ℝ ι) :
    ∫ η : EuclideanSpace ℝ ι, 𝐞 (inner ℝ η u) •
      (eval (fun i => ((η i : ℝ) : ℂ)) (monomial s (1 : ℂ)) * (Real.exp (-(b * ‖η‖ ^ 2)) : ℂ)) =
      eval (fun i => ((u i : ℝ) : ℂ)) (rS b s) * (Real.exp (-(Real.pi ^ 2 / b * ‖u‖ ^ 2)) : ℂ) := by sorry

alias «PositivityTheory».«SiegelWeilFormula».«KFPB».«integral_mono'» := P2M_PositivityTheory_SiegelWeilFormula_KFPB_integral_mono__4b40e6adf110
