-- Prove2me | Theorems.Thm_Projectivization_mapEquiv_continuous_of_finiteDim
-- name    : Projectivization.mapEquiv_continuous_of_finiteDim
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:51:58.656863+00:00
-- url     : https://prove2.me/theorems/2e570356-6c24-4354-8672-c923e4cbc06f
-- title:
--   Projectivization: map Equiv continuous of finite Dim
-- statement:
--   In finite-dim normed setting over `RCLike`, every linear self-equivalence
--   of `V` is continuous (Banach), so its induced projectivization map is
--   continuous for free.
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/LinearAlgebra/Projectivization/Topology.lean#L259-L261
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/LinearAlgebra/Projectivization/Topology.lean#L259-L261

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
variable [RCLike K] [NormedAddCommGroup V] [NormedSpace K V] [FiniteDimensional K V]

theorem Projectivization.mapEquiv_continuous_of_finiteDim (e : V ≃ₗ[K] V) :
    Continuous (mapEquiv e) := by sorry
