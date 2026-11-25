-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CubeLift_tri_p__1bb88d54b808
-- name    : P2M_GlobalTheory_CubeLift_tri_p__1bb88d54b808
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:04:57.220808+00:00
-- url     : https://prove2.me/theorems/1922bd7e-b838-4728-9a89-480a755268dd
-- title:
--   P2 M Global Theory Cube Lift tri p  1bb88d54b808: P2 M Global Theory Cube Lift tri p  1bb88d54b808
-- statement:
--   The P2 M Global Theory Cube Lift tri p  1bb88d54b808 construction uses the P2 M Global Theory Cube Lift tri p  1bb88d54b808 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsNilpotentOfRd.lean#L220-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsNilpotentOfRd.lean#L220-L220

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

theorem P2M_GlobalTheory_CubeLift_tri_p__1bb88d54b808 (a b c : X →+ Y) : (tri a b c).comp p₃ = c := by sorry

alias «GlobalTheory».«CubeLift».«tri_p₃» := P2M_GlobalTheory_CubeLift_tri_p__1bb88d54b808
