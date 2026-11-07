-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_isUnit_qPoch
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.isUnit_qPoch
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:09:20.821535+00:00
-- url     : https://prove2.me/theorems/999b70b0-2e2d-46dd-a564-8cd2a02cd19b
-- title:
--   Jacobi Triple Product Core: is Unit q Poch
-- statement:
--   The Jacobi Triple Product Core construction uses the is Unit q Poch property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L504-L506
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L504-L506

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.isUnit_qPoch (m : ℕ) : IsUnit (qPoch (q ^ 2) (q ^ 2) m : R) := by sorry
