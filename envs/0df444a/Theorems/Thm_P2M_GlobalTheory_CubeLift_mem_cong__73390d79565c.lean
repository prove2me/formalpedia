-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CubeLift_mem_cong__73390d79565c
-- name    : P2M_GlobalTheory_CubeLift_mem_cong__73390d79565c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:50:29.336518+00:00
-- url     : https://prove2.me/theorems/5647aa28-7387-475e-86f0-66e46c623059
-- title:
--   P2 M Global Theory Cube Lift mem cong  73390d79565c: P2 M Global Theory Cube Lift mem cong  73390d79565c
-- statement:
--   The P2 M Global Theory Cube Lift mem cong  73390d79565c construction uses the P2 M Global Theory Cube Lift mem cong  73390d79565c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsNilpotentOfRd.lean#L166-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsNilpotentOfRd.lean#L166-L167

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

theorem P2M_GlobalTheory_CubeLift_mem_cong__73390d79565c {I : Ideal A} {u : (A[X])ˣ} : u ∈ cong I ↔ rd I (u.val - 1) = 0 := by sorry

alias «GlobalTheory».«CubeLift».«mem_cong'» := P2M_GlobalTheory_CubeLift_mem_cong__73390d79565c
