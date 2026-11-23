-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_matrix_ext_mulVec_52bd164b4cc0
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_matrix_ext_mulVec_52bd164b4cc0
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:21:52.450936+00:00
-- url     : https://prove2.me/theorems/c8fb935b-f4f0-45eb-ae7f-59fdc1de047d
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume matrix ext mul Vec 52bd164b4cc0: P2 M Ground Theory Heights  Heights Finite Covolume matrix ext mul Vec 52bd164b4cc0
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume matrix ext mul Vec 52bd164b4cc0 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume matrix ext mul Vec 52bd164b4cc0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusMatrix.lean#L90-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusMatrix.lean#L90-L93

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
variable [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_matrix_ext_mulVec_52bd164b4cc0 {A B : Matrix ι ι ℂ} (h : ∀ z, A *ᵥ z = B *ᵥ z) : A = B := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«matrix_ext_mulVec» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_matrix_ext_mulVec_52bd164b4cc0
