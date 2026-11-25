-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_DegLTEventuallyConst_eq_of_unitSteps_eq_zero_9eea2be60e1e
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_DegLTEventuallyConst_eq_of_unitSteps_eq_zero_9eea2be60e1e
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:31:32.986136+00:00
-- url     : https://prove2.me/theorems/d798f6e8-91f9-4f94-bcd1-7fbdae68302e
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Deg LTEventually Const eq of unit Steps eq zero 9eea2be60e1e: P2 M Ground Theory Heights  Heights Numbers DVR Deg LTEventually Const eq of unit Steps eq
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Deg LTEventually Const eq of unit Steps eq zero 9eea2be60e1e construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Deg LTEventually Const eq of unit Steps eq zero 9eea2be60e1e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PDegLTEventuallyConst.lean#L9-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PDegLTEventuallyConst.lean#L9-L54

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDegLTEventuallyConst
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
open GroundTheory.Heights₂.Heights.NumbersDVR.DegLTEventuallyConst

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_DegLTEventuallyConst_eq_of_unitSteps_eq_zero_9eea2be60e1e {K : Type} [Fintype K] [DecidableEq K] (g : (K → ℤ) → ℤ)
    (N : K → ℤ) (h : ∀ m, N ≤ m → ∀ k, g m - g (m - Pi.single k 1) = 0) :
    ∀ d : ℕ, ∀ m, N ≤ m → ∑ k, (m k - N k).toNat = d → g m = g N := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«DegLTEventuallyConst».«eq_of_unitSteps_eq_zero» := P2M_GroundTheory_Heights__Heights_NumbersDVR_DegLTEventuallyConst_eq_of_unitSteps_eq_zero_9eea2be60e1e
