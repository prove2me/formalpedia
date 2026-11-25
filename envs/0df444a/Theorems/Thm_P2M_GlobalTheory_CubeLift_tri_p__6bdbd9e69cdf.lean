-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CubeLift_tri_p__6bdbd9e69cdf
-- name    : P2M_GlobalTheory_CubeLift_tri_p__6bdbd9e69cdf
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:04:57.067798+00:00
-- url     : https://prove2.me/theorems/3b4a4d0e-4760-468c-a617-4ad2668c1623
-- title:
--   P2 M Global Theory Cube Lift tri p  6bdbd9e69cdf: P2 M Global Theory Cube Lift tri p  6bdbd9e69cdf
-- statement:
--   The P2 M Global Theory Cube Lift tri p  6bdbd9e69cdf construction uses the P2 M Global Theory Cube Lift tri p  6bdbd9e69cdf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsNilpotentOfRd.lean#L218-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsNilpotentOfRd.lean#L218-L218

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsNilpotentOfRd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AddMonoidAlgebra
open GlobalTheory GlobalTheory.CubeLift
variable {A : Type} [CommRing A] {X Y W : Type} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup W]

theorem P2M_GlobalTheory_CubeLift_tri_p__6bdbd9e69cdf (a b c : X →+ Y) : (tri a b c).comp p₁ = a := by sorry

alias «GlobalTheory».«CubeLift».«tri_p₁» := P2M_GlobalTheory_CubeLift_tri_p__6bdbd9e69cdf
