-- Prove2me | Theorems.Thm_Projectivization_mapEquiv_continuous
-- name    : Projectivization.mapEquiv_continuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:51:50.196803+00:00
-- url     : https://prove2.me/theorems/e8f7d5a2-a7db-4747-ac2c-ea7a8581ab6d
-- title:
--   Projectivization: map Equiv continuous
-- statement:
--   The `mapEquiv` of a continuous linear equivalence is continuous.
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/LinearAlgebra/Projectivization/Topology.lean#L150-L152
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/LinearAlgebra/Projectivization/Topology.lean#L150-L152

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

theorem Projectivization.mapEquiv_continuous (e : V ≃ₗ[K] V) (he : Continuous (e : V → V)) :
    Continuous (mapEquiv e) := by sorry
