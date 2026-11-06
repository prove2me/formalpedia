-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_LocalMeromorphicDifferential_localDifferentialLattice_eq_analyticRegular
-- name    : QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.localDifferentialLattice_eq_analyticRegular
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:05:40.621693+00:00
-- url     : https://prove2.me/theorems/9fe13873-e9e7-428e-a324-8f2687ce4624
-- title:
--   Local Meromorphic Differential: local Differential Lattice eq analytic Regular
-- statement:
--   The regular df lattice equals the true analytic no-pole submodule.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/LocalMeromorphicDifferential.lean#L140-L144
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/LocalMeromorphicDifferential.lean#L140-L144

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
variable [IsDiscreteValuationRing (localValuationRing K a)]

theorem QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.localDifferentialLattice_eq_analyticRegular (e : (KaehlerDifferential ℂ K) ≃ₗ[K] K) :
    localDifferentialLattice K a =
      analyticRegularDifferentialSubmodule K a := by sorry
