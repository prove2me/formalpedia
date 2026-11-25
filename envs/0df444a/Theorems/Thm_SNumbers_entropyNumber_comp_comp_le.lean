-- Prove2me | Theorems.Thm_SNumbers_entropyNumber_comp_comp_le
-- name    : SNumbers.entropyNumber_comp_comp_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:18:19.803265+00:00
-- url     : https://prove2.me/theorems/9d2621ce-85da-4127-ac7f-143bce11c14a
-- title:
--   SNumbers: entropy Number comp comp le
-- statement:
--   **(S3) Ideal property**, a corollary of multiplicativity applied twice
--   (once in each slot) together with `e_0 ≤ ‖·‖`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Entropy.lean#L479-L493
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Entropy.lean#L479-L493

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

theorem SNumbers.entropyNumber_comp_comp_le (B : Y →L[𝕜] Z) (S : X →L[𝕜] Y) (A : W →L[𝕜] X)
    (n : ℕ) :
    entropyNumber (B.comp (S.comp A)) n ≤ ‖B‖ * entropyNumber S n * ‖A‖ := by sorry
