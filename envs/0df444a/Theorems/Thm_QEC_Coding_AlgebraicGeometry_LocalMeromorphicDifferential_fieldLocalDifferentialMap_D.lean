-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_LocalMeromorphicDifferential_fieldLocalDifferentialMap_D
-- name    : QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.fieldLocalDifferentialMap_D
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:05:33.868638+00:00
-- url     : https://prove2.me/theorems/1d55c299-023a-4ddf-9de6-5210482625da
-- title:
--   Local Meromorphic Differential: field Local Differential Map D
-- statement:
--   Universal df maps to the derivative of its actual punctured local germ.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/LocalMeromorphicDifferential.lean#L42-L45
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/LocalMeromorphicDifferential.lean#L42-L45

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_DiscreteAnalyticOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_MeromorphicGermDifferentiation
import Mathlib.RingTheory.Kaehler.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_LocalMeromorphicDifferential
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open Filter Topology
noncomputable section
variable (K : Type*) [Field K] [Algebra ℂ K] (a : ℂ)
attribute [local instance] QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential._p2m_local_instance_8465ba921d_22
variable [Algebra K (MeromorphicGermRing a)] [IsScalarTower ℂ K (MeromorphicGermRing a)]

theorem QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.fieldLocalDifferentialMap_D (f : K) :
    fieldLocalDifferentialMap K a (KaehlerDifferential.D ℂ K f) =
      germDerivative a ((IsScalarTower.toAlgHom ℂ K (MeromorphicGermRing a)) f) := by sorry
