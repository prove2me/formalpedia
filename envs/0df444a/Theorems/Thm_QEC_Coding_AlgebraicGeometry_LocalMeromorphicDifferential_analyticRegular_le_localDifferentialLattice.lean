-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_LocalMeromorphicDifferential_analyticRegular_le_localDifferentialLattice
-- name    : QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.analyticRegular_le_localDifferentialLattice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:06:08.000301+00:00
-- url     : https://prove2.me/theorems/8b0b6631-d595-446e-9a9f-dfa3fccdf8b1
-- title:
--   Local Meromorphic Differential: analytic Regular le local Differential Lattice
-- statement:
--   The DVR order gap forces a no-pole differential coefficient into the regular lattice.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/LocalMeromorphicDifferential.lean#L115-L137
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/LocalMeromorphicDifferential.lean#L115-L137

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

theorem QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.analyticRegular_le_localDifferentialLattice (e : (KaehlerDifferential ℂ K) ≃ₗ[K] K) :
    analyticRegularDifferentialSubmodule K a ≤
      localDifferentialLattice K a := by sorry
