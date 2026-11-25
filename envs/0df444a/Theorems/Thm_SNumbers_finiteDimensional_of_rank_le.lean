-- Prove2me | Theorems.Thm_SNumbers_finiteDimensional_of_rank_le
-- name    : SNumbers.finiteDimensional_of_rank_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:12:37.790927+00:00
-- url     : https://prove2.me/theorems/7fa90004-f5dd-44a0-93e4-6f589141c5ba
-- title:
--   SNumbers: finite Dimensional of rank le
-- statement:
--   A subspace of dimension at most `n` is finite-dimensional.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Basic.lean#L166-L168
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Basic.lean#L166-L168

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

theorem SNumbers.finiteDimensional_of_rank_le {V : Submodule 𝕜 X}
    (hV : Module.rank 𝕜 V ≤ (n : Cardinal)) : FiniteDimensional 𝕜 V := by sorry
