-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_MeromorphicGerms_normalizedGermValue_comp
-- name    : QEC.Coding.AlgebraicGeometry.MeromorphicGerms.normalizedGermValue_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:52:05.209893+00:00
-- url     : https://prove2.me/theorems/34562dc2-3e75-4346-9bc2-9f1ddcda7f02
-- title:
--   Meromorphic Germs: normalized Germ Value comp
-- statement:
--   The Meromorphic Germs construction uses the normalized Germ Value comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/MeromorphicManifoldNormalForm.lean#L20-L32
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/MeromorphicManifoldNormalForm.lean#L20-L32

import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_MeromorphicManifoldNormalForm
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open Filter Topology
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.MeromorphicGerms.normalizedGermValue_comp (f g : ℂ → ℂ) (x : ℂ)
    (hf : MeromorphicAt f (g x)) (hg : AnalyticAt ℂ g x)
    (ht : Tendsto g (𝓝[≠] x) (𝓝[≠] (g x))) :
    toMeromorphicNFAt (f ∘ g) x x = toMeromorphicNFAt f (g x) (g x) := by sorry
