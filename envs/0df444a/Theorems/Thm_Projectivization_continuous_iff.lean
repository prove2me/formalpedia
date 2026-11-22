-- Prove2me | Theorems.Thm_Projectivization_continuous_iff
-- name    : Projectivization.continuous_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:51:52.541005+00:00
-- url     : https://prove2.me/theorems/90ba3183-e729-4be1-84eb-43d44282199e
-- title:
--   Projectivization: continuous iff
-- statement:
--   The Projectivization construction uses the continuous iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/LinearAlgebra/Projectivization/Topology.lean#L91-L92
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/LinearAlgebra/Projectivization/Topology.lean#L91-L92

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
variable {α : Type*} [TopologicalSpace α]

theorem Projectivization.continuous_iff {f : ℙ K V → α} : Continuous f ↔ Continuous (f ∘ mk' K) := by sorry
