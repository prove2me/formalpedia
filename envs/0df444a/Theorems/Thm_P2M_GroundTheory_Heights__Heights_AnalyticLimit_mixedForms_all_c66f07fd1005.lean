-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_mixedForms_all_c66f07fd1005
-- name    : P2M_GroundTheory_Heights__Heights_AnalyticLimit_mixedForms_all_c66f07fd1005
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:47:22.010876+00:00
-- url     : https://prove2.me/theorems/6b56fefd-faba-4af4-8bfe-3269918297f6
-- title:
--   P2 M Ground Theory Heights  Heights Analytic Limit mixed Forms all c66f07fd1005: P2 M Ground Theory Heights  Heights Analytic Limit mixed Forms all c66f07fd1005
-- statement:
--   The P2 M Ground Theory Heights  Heights Analytic Limit mixed Forms all c66f07fd1005 construction uses the P2 M Ground Theory Heights  Heights Analytic Limit mixed Forms all c66f07fd1005 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/UniformIntegrability.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/UniformIntegrability.lean#L15-L17

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_GreenMassZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_GreenMassStep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_GreenMassReplace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_GreenMassError
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_UniformIntegrability
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.AnalyticLimit
open ReciprocityTheory.AnForm.M (mInt)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (ell errE)
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_AnalyticLimit_mixedForms_all_c66f07fd1005 {W : Type} [TopologicalSpace W] {D : ℕ} (Om : ReciprocityTheory.AnForm.M.LocPot W)
    (T : Fin (D + 1) → ReciprocityTheory.AnForm.M.LocPot W) : mixedForms Om T (D + 1) = T := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AnalyticLimit».«mixedForms_all» := P2M_GroundTheory_Heights__Heights_AnalyticLimit_mixedForms_all_c66f07fd1005
