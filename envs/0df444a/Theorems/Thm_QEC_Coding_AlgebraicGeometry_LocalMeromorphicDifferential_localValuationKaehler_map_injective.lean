-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_LocalMeromorphicDifferential_localValuationKaehler_map_injective
-- name    : QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.localValuationKaehler_map_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:10:03.646579+00:00
-- url     : https://prove2.me/theorems/c243a5a4-5b60-49b8-8faa-fa1eba5d19e8
-- title:
--   Local Meromorphic Differential: local Valuation Kaehler map injective
-- statement:
--   Actual residue evaluation and a genuine positive-order DVR parameter prove local differential injection for an essentially finite-type valuation ring.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/MeromorphicValuationDifferentials.lean#L76-L84
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/MeromorphicValuationDifferentials.lean#L76-L84

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_LocalKaehlerCyclic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_LocalMeromorphicDifferential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AnalyticGermEvaluation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_MeromorphicValuationDifferentials
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder
noncomputable section
variable (K : Type*) [Field K] [Algebra ℂ K] (a : ℂ)
attribute [local instance] QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.MeromorphicValuationDifferentialsDictionary004
variable [Algebra K (MeromorphicGermRing a)] [IsScalarTower ℂ K (MeromorphicGermRing a)]
local notation "V" => localValuationRing K a
attribute [local instance] QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.MeromorphicValuationDifferentialsDictionary005
attribute [local instance] QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.MeromorphicValuationDifferentialsDictionary006
attribute [local instance] QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.MeromorphicValuationDifferentialsDictionary007
attribute [local instance] QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.MeromorphicValuationDifferentialsDictionary008
attribute [local instance] QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.MeromorphicValuationDifferentialsDictionary009
attribute [local instance] QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.MeromorphicValuationDifferentialsDictionary010
attribute [local instance] QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.MeromorphicValuationDifferentialsDictionary011
attribute [local instance] QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.MeromorphicValuationDifferentialsDictionary012

theorem QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.localValuationKaehler_map_injective
    [IsDiscreteValuationRing V] [Algebra.EssFiniteType ℂ V] :
    Function.Injective (KaehlerDifferential.map ℂ ℂ V K) := by sorry
