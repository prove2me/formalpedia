-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_sub_right_ae1f47de359a
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_sub_right_ae1f47de359a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:20:15.368203+00:00
-- url     : https://prove2.me/theorems/3228674b-b9c2-4121-8499-c36f905e8db3
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume h Form sub right ae1f47de359a: P2 M Ground Theory Heights  Heights Finite Covolume h Form sub right ae1f47de359a
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume h Form sub right ae1f47de359a construction uses the P2 M Ground Theory Heights  Heights Finite Covolume h Form sub right ae1f47de359a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusMatrix.lean#L26-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusMatrix.lean#L26-L27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentModulusMatrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open Matrix
noncomputable section
variable {ι : Type*} [Fintype ι]
variable (H : Matrix ι ι ℂ)

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_sub_right_ae1f47de359a (u z z' : ι → ℂ) : hForm H u (z - z') = hForm H u z - hForm H u z' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«hForm_sub_right» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_sub_right_ae1f47de359a
