-- Prove2me | Theorems.Thm_SNumbers_ne_top_of_rank_le_of_lt_rank
-- name    : SNumbers.ne_top_of_rank_le_of_lt_rank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:12:28.821975+00:00
-- url     : https://prove2.me/theorems/45e43087-5b45-45a9-b6f6-1b0bbcc8f009
-- title:
--   SNumbers: ne top of rank le of lt rank
-- statement:
--   A subspace of dimension at most `n` is proper when `dim X > n`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Basic.lean#L171-L176
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Basic.lean#L171-L176

module
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Dimension.LinearMap
public import Definitions.Def_SNumbers_Basic
set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal
open SNumbers
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X] {n : ℕ}

theorem SNumbers.ne_top_of_rank_le_of_lt_rank {V : Submodule 𝕜 X}
    (hV : Module.rank 𝕜 V ≤ (n : Cardinal)) (h : (n : Cardinal) < Module.rank 𝕜 X) :
    V ≠ ⊤ := by sorry
