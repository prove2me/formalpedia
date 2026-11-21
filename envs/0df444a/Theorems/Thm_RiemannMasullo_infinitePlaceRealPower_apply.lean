-- Prove2me | Theorems.Thm_RiemannMasullo_infinitePlaceRealPower_apply
-- name    : RiemannMasullo.infinitePlaceRealPower_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T01:56:38.407011+00:00
-- url     : https://prove2.me/theorems/08a283f7-79ae-4181-ac18-bed808565fe4
-- title:
--   Riemann Masullo: infinite Place Real Power apply
-- statement:
--   Paper: Definition A.2.2.5, p. 547. Under the archimedean embedding the value
--   is the positive real power itself, including at a complex place.
--
--   Source: https://github.com/mccorvie/riemann-masullo/blob/1d230a0b2ed5968e8c5134784934df4e8a8521b8/RiemannMasullo/AppA_AlgebraicNT/Sec2.lean#L279-L293
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/1d230a0b2ed5968e8c5134784934df4e8a8521b8/RiemannMasullo/AppA_AlgebraicNT/Sec2.lean#L279-L293

module
public import Mathlib
public import Definitions.Def_RiemannMasullo_InfinitePlaceRealPowers
set_option autoImplicit false
@[expose] public section
public section
noncomputable section
open RiemannMasullo
open Function NumberField IsDedekindDomain Topology
open InfinitePlace.Completion
open scoped Classical NNRat NNReal NumberField.AdeleRing Pointwise
variable (F : Type*) [Field F] [NumberField F]

theorem RiemannMasullo.infinitePlaceRealPower_apply (v : InfinitePlace F) (r : ℝ) (t : ℝ≥0ˣ) :
    extensionEmbedding v (infinitePlaceRealPower F v r t).val = (((t.val : ℝ) ^ r : ℝ) : ℂ) := by sorry
