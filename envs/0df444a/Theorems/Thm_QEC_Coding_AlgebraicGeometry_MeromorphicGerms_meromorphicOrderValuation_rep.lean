-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_MeromorphicGerms_meromorphicOrderValuation_rep
-- name    : QEC.Coding.AlgebraicGeometry.MeromorphicGerms.meromorphicOrderValuation_rep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:01:36.873092+00:00
-- url     : https://prove2.me/theorems/738b339e-4e01-4f00-8dfd-c493d908e57c
-- title:
--   Meromorphic Germs: meromorphic Order Valuation rep
-- statement:
--   The Meromorphic Germs construction uses the meromorphic Order Valuation rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/MeromorphicGerms.lean#L63-L65
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/MeromorphicGerms.lean#L63-L65

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

theorem QEC.Coding.AlgebraicGeometry.MeromorphicGerms.meromorphicOrderValuation_rep (x : ℂ) (f : ℂ → ℂ) (hf : MeromorphicAt f x) :
    meromorphicOrderValuation x ⟨(f : Germ (𝓝[≠] x) ℂ),f,hf,rfl⟩ =
      meromorphicOrderAt f x := by sorry
