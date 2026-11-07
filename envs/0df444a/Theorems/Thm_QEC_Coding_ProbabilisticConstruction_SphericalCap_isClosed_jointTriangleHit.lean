-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_isClosed_jointTriangleHit
-- name    : QEC.Coding.ProbabilisticConstruction.SphericalCap.isClosed_jointTriangleHit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:22:06.34337+00:00
-- url     : https://prove2.me/theorems/ec7a1bee-b7a7-4fe0-8bd8-744ad5098016
-- title:
--   Spherical Cap: is Closed joint Triangle Hit
-- statement:
--   The Spherical Cap construction uses the is Closed joint Triangle Hit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/JointTriangleHit.lean#L48-L52
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/JointTriangleHit.lean#L48-L52

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_TriangleGeometry
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_JointTriangleHit
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set
open scoped BigOperators

theorem QEC.Coding.ProbabilisticConstruction.SphericalCap.isClosed_jointTriangleHit : IsClosed
    {d : TriangleHitData | d.2.2.2 ∈ triangleHit d.1 d.2.1 d.2.2.1} := by sorry
