-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_PushForwardOpen_det_fderiv_oneVariable_ne_zero_c5cb4f8989fc
-- name    : P2M_GroundTheory_Heights__Heights_Targets_PushForwardOpen_det_fderiv_oneVariable_ne_zero_c5cb4f8989fc
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:57:01.769782+00:00
-- url     : https://prove2.me/theorems/6b4456e7-58a9-584e-b587-76dfcb5fb76c
-- title:
--   P2 M Ground Theory Heights  Heights Targets Push Forward Open det fderiv one Variable ne zero c5cb4f8989fc: P2 M Ground Theory Heights  Heights Targets Push Forward Open det fderiv one Variable ne zer
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Push Forward Open det fderiv one Variable ne zero c5cb4f8989fc construction uses the P2 M Ground Theory Heights  Heights Targets Push Forward Open det fderiv one Variable ne zero c5cb4f8989fc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/DivPushResSideInhabitants.lean#L21-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/DivPushResSideInhabitants.lean#L21-L31

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_KerEqBotOfCoord
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsPushForwardOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRegularFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRegularDens
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_DivPushResSideInhabitants
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

theorem P2M_GroundTheory_Heights__Heights_Targets_PushForwardOpen_det_fderiv_oneVariable_ne_zero_c5cb4f8989fc {F : ℂ → ℂ} {d : ℂ} {w : Fin 1 → ℂ}
    (hF : HasDerivAt F d (w 0)) (hd : d ≠ 0) :
    LinearMap.det (fderiv ℂ (fun v : Fin 1 → ℂ => fun _ : Fin 1 => F (v 0)) w :
      (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ)) ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«PushForwardOpen».«det_fderiv_oneVariable_ne_zero» := P2M_GroundTheory_Heights__Heights_Targets_PushForwardOpen_det_fderiv_oneVariable_ne_zero_c5cb4f8989fc
