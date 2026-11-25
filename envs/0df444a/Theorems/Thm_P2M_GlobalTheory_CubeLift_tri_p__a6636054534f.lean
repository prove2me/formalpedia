-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CubeLift_tri_p__a6636054534f
-- name    : P2M_GlobalTheory_CubeLift_tri_p__a6636054534f
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:05:00.093205+00:00
-- url     : https://prove2.me/theorems/c348e607-96b3-4371-80ec-de41af72667a
-- title:
--   P2 M Global Theory Cube Lift tri p  a6636054534f: P2 M Global Theory Cube Lift tri p  a6636054534f
-- statement:
--   The P2 M Global Theory Cube Lift tri p  a6636054534f construction uses the P2 M Global Theory Cube Lift tri p  a6636054534f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsNilpotentOfRd.lean#L219-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsNilpotentOfRd.lean#L219-L219

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

theorem P2M_GlobalTheory_CubeLift_tri_p__a6636054534f (a b c : X →+ Y) : (tri a b c).comp p₂ = b := by sorry

alias «GlobalTheory».«CubeLift».«tri_p₂» := P2M_GlobalTheory_CubeLift_tri_p__a6636054534f
