-- Prove2me | Theorems.Thm_SNumbers_mul_mem_entropySet_comp
-- name    : SNumbers.mul_mem_entropySet_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:18:25.457038+00:00
-- url     : https://prove2.me/theorems/56f5d7c3-c00c-5d73-819a-855942697ebc
-- title:
--   SNumbers: mul mem entropy Set comp
-- statement:
--   Covering step behind multiplicativity. Let `B(B_Y)` be covered by `2 ^ n`
--   balls of radius `β` with centres `z`, let `S(B_X)` be covered by `2 ^ m` balls
--   of radius `δ` with centres `y`, and let `c` be a scalar with `‖c‖ > δ`. Then
--   the `2 ^ (n + m)` points `B y + c • z` cover `(B ∘ S)(B_X)` with radius
--   `‖c‖ · β`: the difference `S x - y` has norm at most `δ < ‖c‖`, so
--   `c⁻¹ • (S x - y)` lies in `B_Y` and its image under `B` is `β`-close to some
--   centre `z`; multiplying back by `c` scales that estimate by `‖c‖`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Entropy.lean#L398-L433
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Entropy.lean#L398-L433

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
variable {𝕜 : Type u} [DenselyNormedField 𝕜]
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

theorem SNumbers.mul_mem_entropySet_comp {B : Y →L[𝕜] Z} {S : X →L[𝕜] Y} {n m : ℕ} {β δ : ℝ}
    (hβ : β ∈ entropySet B n) (hδ : δ ∈ entropySet S m) {c : 𝕜} (hc : δ < ‖c‖) :
    ‖c‖ * β ∈ entropySet (B.comp S) (n + m) := by sorry
