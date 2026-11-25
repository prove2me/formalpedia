-- Prove2me | Theorems.Thm_P2M_GlobalTheory_OrbitGrowth_grow_inv__bac8081d7f9f
-- name    : P2M_GlobalTheory_OrbitGrowth_grow_inv__bac8081d7f9f
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:07:13.525323+00:00
-- url     : https://prove2.me/theorems/f5d7a0ae-6cb9-48e2-99a9-07b450bb1805
-- title:
--   P2 M Global Theory Orbit Growth grow inv  bac8081d7f9f: P2 M Global Theory Orbit Growth grow inv  bac8081d7f9f
-- statement:
--   The P2 M Global Theory Orbit Growth grow inv  bac8081d7f9f construction uses the P2 M Global Theory Orbit Growth grow inv  bac8081d7f9f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/MulApply.lean#L78-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/MulApply.lean#L78-L85

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_MulApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.OrbitGrowth
variable {M : Type} [AddCommGroup M] [Module ℂ M]

theorem P2M_GlobalTheory_OrbitGrowth_grow_inv__bac8081d7f9f {A : Subalgebra ℂ (Module.End ℂ M)} {W : Submodule ℂ M} {c : Module.End ℂ M}
    (hc : ∀ x ∈ W, c x ∈ W) (hcomm : ∀ a ∈ A, c * a = a * c) {x : M} (hx : x ∈ grow A W) :
    c x ∈ grow A W := by sorry

alias «GlobalTheory».«OrbitGrowth».«grow_inv'» := P2M_GlobalTheory_OrbitGrowth_grow_inv__bac8081d7f9f
