-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_VolumeFormIntComb_proof_a5a660311a82
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_VolumeFormIntComb_proof_a5a660311a82
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T02:48:02.247892+00:00
-- url     : https://prove2.me/theorems/5b0e72bf-fa34-4644-97b9-2e87436e507c
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Volume Form Int Comb proof a5a660311a82: P2 M Ground Theory Heights  Heights Finite Covolume Volume Form Int Comb proof a5a660311a82
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Volume Form Int Comb proof a5a660311a82 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Volume Form Int Comb proof a5a660311a82 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PVolumeFormIntComb.lean#L11-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PVolumeFormIntComb.lean#L11-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PVolumeFormIntComb
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open Module Matrix
variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  (d : ℕ) [Fact (finrank ℝ V = d)]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_VolumeFormIntComb_proof_a5a660311a82 : VolumeFormIntComb.Statement V d := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«VolumeFormIntComb».«proof» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_VolumeFormIntComb_proof_a5a660311a82
