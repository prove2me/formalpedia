-- Prove2me | Theorems.Thm_SNumbers_ne_bot_of_rank_quotient_le_of_lt_rank
-- name    : SNumbers.ne_bot_of_rank_quotient_le_of_lt_rank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:51:36.050305+00:00
-- url     : https://prove2.me/theorems/298de6a7-ae08-47f8-b385-23b76978e0ab
-- title:
--   SNumbers: ne bot of rank quotient le of lt rank
-- statement:
--   A subspace of codimension at most `n` is nonzero when `dim X > n`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Basic.lean#L179-L184
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Basic.lean#L179-L184

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

theorem SNumbers.ne_bot_of_rank_quotient_le_of_lt_rank {M : Submodule 𝕜 X}
    (hM : Module.rank 𝕜 (X ⧸ M) ≤ (n : Cardinal)) (h : (n : Cardinal) < Module.rank 𝕜 X) :
    M ≠ ⊥ := by sorry
