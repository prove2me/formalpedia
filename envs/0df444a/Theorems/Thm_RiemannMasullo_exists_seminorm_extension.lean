-- Prove2me | Theorems.Thm_RiemannMasullo_exists_seminorm_extension
-- name    : RiemannMasullo.exists_seminorm_extension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:16:35.384501+00:00
-- url     : https://prove2.me/theorems/7a6f5b02-5348-446f-9c68-087ffff4c0bd
-- title:
--   Riemann Masullo: exists seminorm extension
-- statement:
--   A continuous seminorm extends along a linear inducing map into a polynormable space.
--
--   Source: https://github.com/mccorvie/riemann-masullo/blob/1d230a0b2ed5968e8c5134784934df4e8a8521b8/RiemannMasullo/ForMathlib/Analysis/LocallyConvex/WithSeminorms.lean#L17-L42
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/1d230a0b2ed5968e8c5134784934df4e8a8521b8/RiemannMasullo/ForMathlib/Analysis/LocallyConvex/WithSeminorms.lean#L17-L42

module
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Definitions.Def_RiemannMasullo_ForMathlib_Analysis_LocallyConvex_WithSeminorms
set_option autoImplicit false
@[expose] public section
public section
open Set Topology
open RiemannMasullo
variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [PolynormableSpace 𝕜 F]

theorem RiemannMasullo.exists_seminorm_extension {f : E →ₗ[𝕜] F} (hf : IsInducing f)
    {p : Seminorm 𝕜 E} (hp : Continuous p) :
    ∃ q : Seminorm 𝕜 F, Continuous q ∧ q.comp f = p := by sorry
