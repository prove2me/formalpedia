-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_oneBlockForms_symm_apply_3b06e6409374
-- name    : P2M_GroundTheory_Heights__Heights_oneBlockForms_symm_apply_3b06e6409374
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:48:38.288617+00:00
-- url     : https://prove2.me/theorems/ae77adbb-cd8e-4a15-983f-b9d03162cc4a
-- title:
--   P2 M Ground Theory Heights  Heights one Block Forms symm apply 3b06e6409374: P2 M Ground Theory Heights  Heights one Block Forms symm apply 3b06e6409374
-- statement:
--   The P2 M Ground Theory Heights  Heights one Block Forms symm apply 3b06e6409374 construction uses the P2 M Ground Theory Heights  Heights one Block Forms symm apply 3b06e6409374 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockStandard.lean#L34-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockStandard.lean#L34-L37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockStandard
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField Matrix
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
omit [NumberField K]

theorem P2M_GroundTheory_Heights__Heights_oneBlockForms_symm_apply_3b06e6409374 {e r : ℕ} (om : Module.Basis (Fin (e + 1)) ℤ (𝓞 K))
    (a : Fin (e + 1)) (j : Fin (r + 1)) :
    oneBlockForms om ((oneBlockIndex e r).symm (a, j)) = Pi.single j ((om a : 𝓞 K) : K) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«oneBlockForms_symm_apply» := P2M_GroundTheory_Heights__Heights_oneBlockForms_symm_apply_3b06e6409374
