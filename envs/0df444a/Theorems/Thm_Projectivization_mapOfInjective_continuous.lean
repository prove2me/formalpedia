-- Prove2me | Theorems.Thm_Projectivization_mapOfInjective_continuous
-- name    : Projectivization.mapOfInjective_continuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:51:56.751504+00:00
-- url     : https://prove2.me/theorems/f4e097a5-88b9-4d94-be16-383b72d93f3c
-- title:
--   Projectivization: map Of Injective continuous
-- statement:
--   A continuous injective linear map descends to a continuous map on
--   projectivizations.
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/LinearAlgebra/Projectivization/Topology.lean#L119-L129
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/LinearAlgebra/Projectivization/Topology.lean#L119-L129

module
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.LinearAlgebra.Projectivization.Action
public import Definitions.Def_BornVolumeLean_Topology_Algebra_MulAction
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Maps.OpenQuotient
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.Topology.Separation.Hausdorff
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_Topology
set_option autoImplicit false
@[expose] public section
public section
open Set Function Topology
open scoped LinearAlgebra.Projectivization
open Projectivization
variable {K V : Type*}
variable [DivisionRing K] [AddCommGroup V] [Module K V]
variable [TopologicalSpace V]
variable {W : Type*} [AddCommGroup W] [Module K W] [TopologicalSpace W]

theorem Projectivization.mapOfInjective_continuous
    (f : V →ₗ[K] W) (hf : Function.Injective f) (hf_cont : Continuous f) :
    Continuous (Projectivization.map f hf) := by sorry
