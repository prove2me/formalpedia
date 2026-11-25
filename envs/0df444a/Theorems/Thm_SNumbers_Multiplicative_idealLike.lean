-- Prove2me | Theorems.Thm_SNumbers_Multiplicative_idealLike
-- name    : SNumbers.Multiplicative.idealLike
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:26:45.405937+00:00
-- url     : https://prove2.me/theorems/f6a8dfdc-a051-40d7-9ab2-3693e13ee2ba
-- title:
--   Multiplicative: ideal Like
-- statement:
--   Multiplicativity implies (S3): `s (B ∘ (S ∘ A)) n ≤ s B 0 · s (S ∘ A) n` and
--   `s (S ∘ A) n ≤ s S n · s A 0`, with `s B 0 = ‖B‖` and `s A 0 = ‖A‖`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Basic.lean#L306-L318
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Basic.lean#L306-L318

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

theorem SNumbers.Multiplicative.idealLike {s : Family 𝕜} (h : Multiplicative s) (h0 : NormAtZero s) :
    IdealLike s := by sorry
