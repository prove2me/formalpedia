-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_MinkowskiVolumeForm_proof_49d10ac54218
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_MinkowskiVolumeForm_proof_49d10ac54218
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T02:44:29.215823+00:00
-- url     : https://prove2.me/theorems/0918cd0d-891a-4b56-9558-afa307b02c03
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Minkowski Volume Form proof 49d10ac54218: P2 M Ground Theory Heights  Heights Finite Covolume Minkowski Volume Form proof 49d10ac54218
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Minkowski Volume Form proof 49d10ac54218 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Minkowski Volume Form proof 49d10ac54218 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PMinkowskiVolumeForm.lean#L11-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PMinkowskiVolumeForm.lean#L11-L108

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PMinkowskiVolumeForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open Module MeasureTheory Submodule
variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  (d : ℕ) [Fact (finrank ℝ V = d)]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_MinkowskiVolumeForm_proof_49d10ac54218 : MinkowskiVolumeForm.Statement V d := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«MinkowskiVolumeForm».«proof» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_MinkowskiVolumeForm_proof_49d10ac54218
