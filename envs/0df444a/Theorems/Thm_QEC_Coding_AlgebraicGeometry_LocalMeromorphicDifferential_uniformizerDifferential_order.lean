-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_LocalMeromorphicDifferential_uniformizerDifferential_order
-- name    : QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.uniformizerDifferential_order
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:05:40.381194+00:00
-- url     : https://prove2.me/theorems/be3eedc4-022f-4d3c-b74d-9fbbc42ddda7
-- title:
--   Local Meromorphic Differential: uniformizer Differential order
-- statement:
--   The genuine local coefficient of dπ has order m-1 for uniformizer order m.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/LocalMeromorphicDifferential.lean#L82-L88
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/LocalMeromorphicDifferential.lean#L82-L88

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

theorem QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.uniformizerDifferential_order (π : (localValuationRing K a))
    (m : ℤ) (hm : 0 < m) (he : (localFieldOrder K a) (π : K) = (m : WithTop ℤ)) :
    meromorphicOrderValuation a
      (fieldLocalDifferentialMap K a (KaehlerDifferential.D ℂ K (π : K))) =
      ((m - 1 : ℤ) : WithTop ℤ) := by sorry
