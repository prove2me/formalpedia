-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_MeromorphicGerms_normalizedGermValue_comp_mul_analyticUnit
-- name    : QEC.Coding.AlgebraicGeometry.MeromorphicGerms.normalizedGermValue_comp_mul_analyticUnit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:57:59.7096+00:00
-- url     : https://prove2.me/theorems/9b2b4da2-a52a-4e06-9099-615aeef8ec46
-- title:
--   Meromorphic Germs: normalized Germ Value comp mul analytic Unit
-- statement:
--   Normal-form value commutes with analytic reparametrization and an analytic unit.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/NormalizedGermUnits.lean#L29-L37
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/NormalizedGermUnits.lean#L29-L37

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_MeromorphicManifoldNormalForm
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_NormalizedGermUnits
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open Filter Topology
open scoped Manifold ContDiff
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.MeromorphicGerms.normalizedGermValue_comp_mul_analyticUnit
    (f g u : ℂ → ℂ) (x : ℂ) (hf : MeromorphicAt f (g x))
    (hg : AnalyticAt ℂ g x) (hu : AnalyticAt ℂ u x) (hunit : u x ≠ 0)
    (ht : Tendsto g (𝓝[≠] x) (𝓝[≠] (g x))) :
    toMeromorphicNFAt ((f ∘ g) * u) x x =
      toMeromorphicNFAt f (g x) (g x) * u x := by sorry
