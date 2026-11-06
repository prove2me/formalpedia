-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_MeromorphicGerms_chartNormalizedMeromorphicFunction_chart
-- name    : QEC.Coding.AlgebraicGeometry.MeromorphicGerms.chartNormalizedMeromorphicFunction_chart
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:52:06.143336+00:00
-- url     : https://prove2.me/theorems/85dc79f3-46c8-4e6e-8882-a2eaa6b87603
-- title:
--   Meromorphic Germs: chart Normalized Meromorphic Function chart
-- statement:
--   The Meromorphic Germs construction uses the chart Normalized Meromorphic Function chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/MeromorphicManifoldNormalForm.lean#L57-L103
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/MeromorphicManifoldNormalForm.lean#L57-L103

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

theorem QEC.Coding.AlgebraicGeometry.MeromorphicGerms.chartNormalizedMeromorphicFunction_chart
    (F : M → ℂ) (hF : ∀ x : M, MeromorphicOn (F ∘ (chartAt ℂ x).symm) (chartAt ℂ x).target)
    (x : M) (z : ℂ) (hz : z ∈ (chartAt ℂ x).target) :
    chartNormalizedMeromorphicFunction F ((chartAt ℂ x).symm z) =
      toMeromorphicNFOn (F ∘ (chartAt ℂ x).symm) (chartAt ℂ x).target z := by sorry
