-- Prove2me | Theorems.Thm_SNumbers_Additive_subadditive
-- name    : SNumbers.Additive.subadditive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:51:40.483417+00:00
-- url     : https://prove2.me/theorems/8a994651-7861-48aa-b4f5-e1d9712da790
-- title:
--   Additive: subadditive
-- statement:
--   Additivity implies (S2): take `m = 0` and use `s T 0 = ‖T‖`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Basic.lean#L298-L302
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Basic.lean#L298-L302

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

theorem SNumbers.Additive.subadditive {s : Family 𝕜} (h : Additive s) (h0 : NormAtZero s) :
    Subadditive s := by sorry
