-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_LocalMeromorphicDifferential_uniformizerDifferential_ne_zero
-- name    : QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.uniformizerDifferential_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:06:01.587773+00:00
-- url     : https://prove2.me/theorems/96ed6ab1-ba71-49d5-b154-cd491b2d28b8
-- title:
--   Local Meromorphic Differential: uniformizer Differential ne zero
-- statement:
--   Positive finite uniformizer order makes its universal differential nonzero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/LocalMeromorphicDifferential.lean#L91-L97
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/LocalMeromorphicDifferential.lean#L91-L97

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

theorem QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.uniformizerDifferential_ne_zero (π : (localValuationRing K a))
    (m : ℤ) (hm : 0 < m) (he : (localFieldOrder K a) (π : K) = (m : WithTop ℤ)) :
    KaehlerDifferential.D ℂ K (π : K) ≠ 0 := by sorry
