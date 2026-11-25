-- Prove2me | Theorems.Thm_SNumbers_norm_mul_mem_entropySet_comp
-- name    : SNumbers.norm_mul_mem_entropySet_comp
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:18:11.259358+00:00
-- url     : https://prove2.me/theorems/8ff36800-cd2e-5ec2-9b44-cbd710e0679d
-- title:
--   SNumbers: norm mul mem entropy Set comp
-- statement:
--   Covering step: applying `B` to the centres turns a cover of `S(B_X)` into
--   a cover of `(B ∘ S)(B_X)` with the radius multiplied by `‖B‖`. This uses only
--   that `B` is Lipschitz, so no assumption on the scalar field is needed.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Entropy.lean#L280-L295
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Entropy.lean#L280-L295

module
public import Definitions.Def_SNumbers_Basic
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Definitions.Def_SNumbers_Entropy
set_option autoImplicit true
@[expose] public section
public section
universe u
open Filter Topology
open SNumbers
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {X Y Z : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

theorem SNumbers.norm_mul_mem_entropySet_comp {B : Y →L[𝕜] Z} {S : X →L[𝕜] Y} {n : ℕ} {ε : ℝ}
    (hB : 0 < ‖B‖) (hε : ε ∈ entropySet S n) :
    ‖B‖ * ε ∈ entropySet (B.comp S) n := by sorry
