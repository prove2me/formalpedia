-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_LocalMeromorphicDifferential_differential_uniformizer_expansion
-- name    : QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.differential_uniformizer_expansion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:05:56.6482+00:00
-- url     : https://prove2.me/theorems/ecdc36d7-3485-4002-8c0d-dbdb89b602a3
-- title:
--   Local Meromorphic Differential: differential uniformizer expansion
-- statement:
--   One-dimensionality expands every universal differential in the genuine dπ basis.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/LocalMeromorphicDifferential.lean#L100-L110
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/LocalMeromorphicDifferential.lean#L100-L110

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

theorem QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.differential_uniformizer_expansion (π : (localValuationRing K a))
    (m : ℤ) (hm : 0 < m) (he : (localFieldOrder K a) (π : K) = (m : WithTop ℤ)) (e : (KaehlerDifferential ℂ K) ≃ₗ[K] K) (ω : (KaehlerDifferential ℂ K)) :
    ∃ f : K, ω = f • KaehlerDifferential.D ℂ K (π : K) := by sorry
