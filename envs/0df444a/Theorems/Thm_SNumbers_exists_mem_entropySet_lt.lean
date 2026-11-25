-- Prove2me | Theorems.Thm_SNumbers_exists_mem_entropySet_lt
-- name    : SNumbers.exists_mem_entropySet_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:17:37.000207+00:00
-- url     : https://prove2.me/theorems/fc587aa8-3b5b-4d0f-bbd3-6de0ebe73d5b
-- title:
--   SNumbers: exists mem entropy Set lt
-- statement:
--   Conversely, below any bound strictly above `e_n S` there is an actual
--   admissible radius. This is how a concrete covering is extracted from a bound
--   on the entropy number.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Entropy.lean#L177-L180
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Entropy.lean#L177-L180

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

theorem SNumbers.exists_mem_entropySet_lt {S : X →L[𝕜] Y} {n : ℕ} {b : ℝ}
    (hb : entropyNumber S n < b) :
    ∃ ε ∈ entropySet S n, ε < b := by sorry
