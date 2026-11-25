-- Prove2me | Theorems.Thm_SNumbers_entropyNumber_comp_le_of_mem
-- name    : SNumbers.entropyNumber_comp_le_of_mem
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:19:03.891852+00:00
-- url     : https://prove2.me/theorems/52fd3261-500d-4b1f-9a1e-20f88327469e
-- title:
--   SNumbers: entropy Number comp le of mem
-- statement:
--   Intermediate form of multiplicativity: for a fixed admissible radius `δ`
--   of `S` and a scalar `c` of norm above `δ`, the infimum over the radii for `B`
--   gives `e_{n+m}(B ∘ S) ≤ ‖c‖ · e_n B`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Entropy.lean#L438-L445
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Entropy.lean#L438-L445

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

theorem SNumbers.entropyNumber_comp_le_of_mem {B : Y →L[𝕜] Z} {S : X →L[𝕜] Y} {n m : ℕ} {δ : ℝ}
    (hδ : δ ∈ entropySet S m) {c : 𝕜} (hc : δ < ‖c‖) :
    entropyNumber (B.comp S) (n + m) ≤ ‖c‖ * entropyNumber B n := by sorry
