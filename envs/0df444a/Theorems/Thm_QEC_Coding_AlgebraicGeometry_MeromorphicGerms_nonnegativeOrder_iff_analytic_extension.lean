-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_MeromorphicGerms_nonnegativeOrder_iff_analytic_extension
-- name    : QEC.Coding.AlgebraicGeometry.MeromorphicGerms.nonnegativeOrder_iff_analytic_extension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:01:43.178717+00:00
-- url     : https://prove2.me/theorems/74a45b88-afed-41a3-85be-023a4dfccd10
-- title:
--   Meromorphic Germs: nonnegative Order iff analytic extension
-- statement:
--   The Meromorphic Germs construction uses the nonnegative Order iff analytic extension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/MeromorphicGerms.lean#L83-L87
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/MeromorphicGerms.lean#L83-L87

import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Order.Filter.Germ.Basic
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.Algebra.Polynomial.AlgebraMap
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_MeromorphicGerms
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open Filter Topology
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.MeromorphicGerms.nonnegativeOrder_iff_analytic_extension (x : ℂ) (f : ℂ → ℂ)
    (hf : MeromorphicAt f x) :
    0 ≤ meromorphicOrderValuation x ⟨(f : Germ (𝓝[≠] x) ℂ),f,hf,rfl⟩ ↔
      ∃ g : ℂ → ℂ, AnalyticAt ℂ g x ∧ f =ᶠ[𝓝[≠] x] g := by sorry
