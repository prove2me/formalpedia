-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_MeromorphicGerms_chartNormalizedMeromorphicFunction_codiscrete
-- name    : QEC.Coding.AlgebraicGeometry.MeromorphicGerms.chartNormalizedMeromorphicFunction_codiscrete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:57:55.283626+00:00
-- url     : https://prove2.me/theorems/ea611b82-5ec2-4b37-aaa0-d81bf9ec5968
-- title:
--   Meromorphic Germs: chart Normalized Meromorphic Function codiscrete
-- statement:
--   The Meromorphic Germs construction uses the chart Normalized Meromorphic Function codiscrete property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/MeromorphicManifoldNormalForm.lean#L129-L148
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/MeromorphicManifoldNormalForm.lean#L129-L148

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

theorem QEC.Coding.AlgebraicGeometry.MeromorphicGerms.chartNormalizedMeromorphicFunction_codiscrete
    (F : M → ℂ) (hF : ∀ x : M, MeromorphicOn (F ∘ (chartAt ℂ x).symm) (chartAt ℂ x).target) :
    F =ᶠ[Filter.codiscrete M] chartNormalizedMeromorphicFunction F := by sorry
