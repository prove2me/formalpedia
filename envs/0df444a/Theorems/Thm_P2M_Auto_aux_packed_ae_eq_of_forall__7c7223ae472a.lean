-- Prove2me | Theorems.Thm_P2M_Auto_aux_packed_ae_eq_of_forall__7c7223ae472a
-- name    : P2M_Auto_aux_packed_ae_eq_of_forall__7c7223ae472a
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:54:00.347415+00:00
-- url     : https://prove2.me/theorems/8ebddd96-31d6-4f89-bc07-5347708c1a81
-- title:
--   P2 M Auto aux packed ae eq of forall  7c7223ae472a: P2 M Auto aux packed ae eq of forall  7c7223ae472a
-- statement:
--   Finite counting-measure packing preserves a coordinatewise a.e. equality, with no
--   measurability hypotheses on either side.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/MultilinearInterpolation.lean#L9240-L9262
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/MultilinearInterpolation.lean#L9240-L9262

module
public import Mathlib.Analysis.Complex.Hadamard
public import Mathlib.Analysis.Complex.CanonicalDecomposition
public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Mathlib.LinearAlgebra.Multilinear.Curry
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Definitions.Def_LeanNct_Auto_MultilinearInterpolation
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Complex.HadamardThreeLines Real Filter Topology ENNReal Asymptotics Set Metric
  MeromorphicOn
open scoped BigOperators
open Auto

theorem P2M_Auto_aux_packed_ae_eq_of_forall__7c7223ae472a {J : ℕ} {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f g : Fin J → X → ℂ}
    (hfg : ∀ j, f j =ᵐ[μ] g j) :
    (fun z : Fin J × X ↦ f z.1 z.2) =ᵐ[(Measure.count : Measure (Fin J)).prod μ]
      fun z ↦ g z.1 z.2 := by sorry

alias «Auto».«aux_packed_ae_eq_of_forall'» := P2M_Auto_aux_packed_ae_eq_of_forall__7c7223ae472a
