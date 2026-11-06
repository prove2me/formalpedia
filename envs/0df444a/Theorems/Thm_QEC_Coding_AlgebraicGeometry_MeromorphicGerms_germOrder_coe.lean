-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_MeromorphicGerms_germOrder_coe
-- name    : QEC.Coding.AlgebraicGeometry.MeromorphicGerms.germOrder_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:02:55.193655+00:00
-- url     : https://prove2.me/theorems/65499c11-1a20-44d8-bd3a-ccea16e2c2a3
-- title:
--   Meromorphic Germs: germ Order coe
-- statement:
--   The Meromorphic Germs construction uses the germ Order coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/MeromorphicGerms.lean#L41-L42
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/MeromorphicGerms.lean#L41-L42

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

theorem QEC.Coding.AlgebraicGeometry.MeromorphicGerms.germOrder_coe (x : ℂ) (f : ℂ → ℂ) :
    germOrder x (f : Germ (𝓝[≠] x) ℂ) = meromorphicOrderAt f x := by sorry
