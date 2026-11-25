-- Prove2me | Theorems.Thm_SNumbers_nontrivial_of_natCast_lt_rank
-- name    : SNumbers.nontrivial_of_natCast_lt_rank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:07:08.617594+00:00
-- url     : https://prove2.me/theorems/4006677f-088b-4673-b2b1-fce359ba31d8
-- title:
--   SNumbers: nontrivial of nat Cast lt rank
-- statement:
--   A space of dimension greater than `n` is nontrivial.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Basic.lean#L161-L163
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Basic.lean#L161-L163

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

theorem SNumbers.nontrivial_of_natCast_lt_rank (h : (n : Cardinal) < Module.rank 𝕜 X) :
    Nontrivial X := by sorry
