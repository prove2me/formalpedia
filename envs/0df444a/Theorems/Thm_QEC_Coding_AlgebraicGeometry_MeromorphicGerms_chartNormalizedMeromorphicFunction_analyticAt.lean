-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_MeromorphicGerms_chartNormalizedMeromorphicFunction_analyticAt
-- name    : QEC.Coding.AlgebraicGeometry.MeromorphicGerms.chartNormalizedMeromorphicFunction_analyticAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:57:57.101811+00:00
-- url     : https://prove2.me/theorems/aa92a19d-ec90-40d4-b977-7586554d2fda
-- title:
--   Meromorphic Germs: chart Normalized Meromorphic Function analytic At
-- statement:
--   The Meromorphic Germs construction uses the chart Normalized Meromorphic Function analytic At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/MeromorphicManifoldNormalForm.lean#L150-L158
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/MeromorphicManifoldNormalForm.lean#L150-L158

import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_MeromorphicManifoldNormalForm
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open Filter Topology
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) ω M]

theorem QEC.Coding.AlgebraicGeometry.MeromorphicGerms.chartNormalizedMeromorphicFunction_analyticAt
    (F : M → ℂ) (hF : ∀ x : M, MeromorphicOn (F ∘ (chartAt ℂ x).symm) (chartAt ℂ x).target)
    (x : M) (z : ℂ) (hz : z ∈ (chartAt ℂ x).target)
    (ho : 0 ≤ meromorphicOrderAt (F ∘ (chartAt ℂ x).symm) z) :
    AnalyticAt ℂ (chartNormalizedMeromorphicFunction F ∘ (chartAt ℂ x).symm) z := by sorry
