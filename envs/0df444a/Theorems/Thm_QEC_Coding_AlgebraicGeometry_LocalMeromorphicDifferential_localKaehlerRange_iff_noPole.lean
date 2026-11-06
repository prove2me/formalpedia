-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_LocalMeromorphicDifferential_localKaehlerRange_iff_noPole
-- name    : QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.localKaehlerRange_iff_noPole
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:02:40.783622+00:00
-- url     : https://prove2.me/theorems/81560f55-2d98-4482-a6e5-3f338aed09ef
-- title:
--   Local Meromorphic Differential: local Kaehler Range iff no Pole
-- statement:
--   The real local Kähler image is detected exactly by analytic coefficient regularity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/LocalMeromorphicDifferential.lean#L189-L194
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/LocalMeromorphicDifferential.lean#L189-L194

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
attribute [local instance] QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential._p2m_local_instance_8465ba921d_158
attribute [local instance] QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential._p2m_local_instance_8465ba921d_159

theorem QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.localKaehlerRange_iff_noPole (e : (KaehlerDifferential ℂ K) ≃ₗ[K] K) (ω : (KaehlerDifferential ℂ K)) :
    ω ∈ ((KaehlerDifferential.D ℂ K).compAlgebraMap (localValuationRing K a)).liftKaehlerDifferential.range ↔
      0 ≤ meromorphicOrderValuation a (fieldLocalDifferentialMap K a ω) := by sorry
