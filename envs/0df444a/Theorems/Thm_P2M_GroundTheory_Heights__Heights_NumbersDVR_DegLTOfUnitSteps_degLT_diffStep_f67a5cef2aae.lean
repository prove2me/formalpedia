-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_DegLTOfUnitSteps_degLT_diffStep_f67a5cef2aae
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_DegLTOfUnitSteps_degLT_diffStep_f67a5cef2aae
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:55:28.706925+00:00
-- url     : https://prove2.me/theorems/d521669b-0914-4b07-8476-c6f18b1303a4
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Deg LTOf Unit Steps deg LT diff Step f67a5cef2aae: P2 M Ground Theory Heights  Heights Numbers DVR Deg LTOf Unit Steps deg LT diff Step f67a5cef2aae
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Deg LTOf Unit Steps deg LT diff Step f67a5cef2aae construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Deg LTOf Unit Steps deg LT diff Step f67a5cef2aae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PDegLTOfUnitSteps.lean#L7-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PDegLTOfUnitSteps.lean#L7-L31

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDegLTOfUnitSteps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_DegLTOfUnitSteps_degLT_diffStep_f67a5cef2aae (h1 : DiffStepExpansion.Statement)
    (h2 : MixedDiffLinear.Statement) (h3 : DegLTClosure.Statement)
    (K : Type) [Fintype K] [DecidableEq K] (n : ℕ) (f : (K → ℤ) → ℤ)
    (hf : ∀ k, DegLT (diffStep (Pi.single k 1) f) n) (b : K → ℤ) :
    DegLT (diffStep b f) n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«DegLTOfUnitSteps».«degLT_diffStep» := P2M_GroundTheory_Heights__Heights_NumbersDVR_DegLTOfUnitSteps_degLT_diffStep_f67a5cef2aae
