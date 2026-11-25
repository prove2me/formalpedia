-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_evalOne_comp_algebraMap_86cab739d7f1
-- name    : P2M_GroundTheory_Heights__Heights_Targets_evalOne_comp_algebraMap_86cab739d7f1
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:02:14.248002+00:00
-- url     : https://prove2.me/theorems/d25d97d0-fe1a-4895-8272-5e94a6fe496b
-- title:
--   P2 M Ground Theory Heights  Heights Targets eval One comp algebra Map 86cab739d7f1: P2 M Ground Theory Heights  Heights Targets eval One comp algebra Map 86cab739d7f1
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets eval One comp algebra Map 86cab739d7f1 construction uses the P2 M Ground Theory Heights  Heights Targets eval One comp algebra Map 86cab739d7f1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/ChartConeObjects.lean#L75-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/ChartConeObjects.lean#L75-L77

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChartA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StChartConeComponent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ChartConeObjects
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
open MvPolynomial
variable {K : Type*} [Fintype K] {ι : K → Type*}

theorem P2M_GroundTheory_Heights__Heights_Targets_evalOne_comp_algebraMap_86cab739d7f1 (i : (k : K) → ι k) :
    (evalOne i).comp (algebraMap _ (ConeRing i)) = (dehom i : MvPolynomial (Σ k, ι k) ℂ →+* DehomRing i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«evalOne_comp_algebraMap» := P2M_GroundTheory_Heights__Heights_Targets_evalOne_comp_algebraMap_86cab739d7f1
