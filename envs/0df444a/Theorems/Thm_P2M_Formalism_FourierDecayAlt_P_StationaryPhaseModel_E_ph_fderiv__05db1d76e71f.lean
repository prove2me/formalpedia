-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_ph_fderiv__05db1d76e71f
-- name    : P2M_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_ph_fderiv__05db1d76e71f
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:55:47.766335+00:00
-- url     : https://prove2.me/theorems/767b9edd-9480-4668-94af-fb8a17b5e7a3
-- title:
--   P2 M Formalism Fourier Decay Alt P Stationary Phase Model E ph fderiv  05db1d76e71f: P2 M Formalism Fourier Decay Alt P Stationary Phase Model E ph fderiv  05db1d76e71f
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Stationary Phase Model E ph fderiv  05db1d76e71f construction uses the P2 M Formalism Fourier Decay Alt P Stationary Phase Model E ph fderiv  05db1d76e71f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L2007-L2011
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L2007-L2011

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StationaryPhaseModel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem P2M_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_ph_fderiv__05db1d76e71f {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (s : ℝ) (x v : E) :
    fderiv ℝ (fun y => quad φ y + s * E_P φ y) x v = fderiv ℝ φ x v - (1 - s) * fderiv ℝ (E_P φ) x v := by sorry

alias «Formalism».«FourierDecayAlt».«P».«StationaryPhaseModel».«E_ph_fderiv'» := P2M_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_ph_fderiv__05db1d76e71f
