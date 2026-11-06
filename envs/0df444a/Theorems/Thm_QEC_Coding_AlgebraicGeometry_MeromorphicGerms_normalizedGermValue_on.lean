-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_MeromorphicGerms_normalizedGermValue_on
-- name    : QEC.Coding.AlgebraicGeometry.MeromorphicGerms.normalizedGermValue_on
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:57:01.777357+00:00
-- url     : https://prove2.me/theorems/8529bea3-6e45-4e2f-9abb-2beb32b3f254
-- title:
--   Meromorphic Germs: normalized Germ Value on
-- statement:
--   The Meromorphic Germs construction uses the normalized Germ Value on property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/MeromorphicManifoldNormalForm.lean#L39-L42
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/MeromorphicManifoldNormalForm.lean#L39-L42

import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_MeromorphicManifoldNormalForm
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open Filter Topology
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.MeromorphicGerms.normalizedGermValue_on (f : ℂ → ℂ) (U : Set ℂ) (x : ℂ)
    (hf : MeromorphicOn f U) (hx : x ∈ U) :
    toMeromorphicNFOn f U x = toMeromorphicNFAt f x x := by sorry
