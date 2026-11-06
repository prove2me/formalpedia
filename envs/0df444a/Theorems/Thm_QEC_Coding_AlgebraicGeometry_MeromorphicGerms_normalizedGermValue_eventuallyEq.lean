-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_MeromorphicGerms_normalizedGermValue_eventuallyEq
-- name    : QEC.Coding.AlgebraicGeometry.MeromorphicGerms.normalizedGermValue_eventuallyEq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:52:08.347204+00:00
-- url     : https://prove2.me/theorems/a5f4646b-29eb-474e-bcb2-4191373fdc9e
-- title:
--   Meromorphic Germs: normalized Germ Value eventually Eq
-- statement:
--   The Meromorphic Germs construction uses the normalized Germ Value eventually Eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/MeromorphicManifoldNormalForm.lean#L34-L37
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/MeromorphicManifoldNormalForm.lean#L34-L37

import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_MeromorphicManifoldNormalForm
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open Filter Topology
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.MeromorphicGerms.normalizedGermValue_eventuallyEq (f g : ℂ → ℂ) (x : ℂ)
    (h : f =ᶠ[𝓝[≠] x] g) :
    toMeromorphicNFAt f x x = toMeromorphicNFAt g x x := by sorry
