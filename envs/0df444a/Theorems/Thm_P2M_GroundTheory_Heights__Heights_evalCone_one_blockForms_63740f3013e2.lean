-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_evalCone_one_blockForms_63740f3013e2
-- name    : P2M_GroundTheory_Heights__Heights_evalCone_one_blockForms_63740f3013e2
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:40:52.383508+00:00
-- url     : https://prove2.me/theorems/f61dda14-58dc-59fd-b2e6-03ec75c6efdc
-- title:
--   P2 M Ground Theory Heights  Heights eval Cone one block Forms 63740f3013e2: P2 M Ground Theory Heights  Heights eval Cone one block Forms 63740f3013e2
-- statement:
--   The P2 M Ground Theory Heights  Heights eval Cone one block Forms 63740f3013e2 construction uses the P2 M Ground Theory Heights  Heights eval Cone one block Forms 63740f3013e2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Examples.lean#L154-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Examples.lean#L154-L156

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Examples
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
open MvPolynomial NumberField
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (n : ι → ℕ) (k₀ : ι)

theorem P2M_GroundTheory_Heights__Heights_evalCone_one_blockForms_63740f3013e2 (c : (k : ι) → Fin (n k + 1)) (j : Fin ((blockAddData n k₀).size + 1)) :
    evalCone (fun _ _ ↦ (1 : ℂ) : Cone n ℂ) (blockForms n k₀ c j) ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«evalCone_one_blockForms» := P2M_GroundTheory_Heights__Heights_evalCone_one_blockForms_63740f3013e2
