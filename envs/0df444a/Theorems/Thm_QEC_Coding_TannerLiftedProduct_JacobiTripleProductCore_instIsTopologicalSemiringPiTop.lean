-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_instIsTopologicalSemiringPiTop
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.instIsTopologicalSemiringPiTop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:07:51.435241+00:00
-- url     : https://prove2.me/theorems/8daabea1-4442-412b-8974-5a57a7982d92
-- title:
--   Jacobi Triple Product Core: inst Is Topological Semiring Pi Top
-- statement:
--   The Jacobi Triple Product Core construction uses the inst Is Topological Semiring Pi Top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L729-L730
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L729-L730

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.instIsTopologicalSemiringPiTop : @IsTopologicalSemiring R piTop _ := by sorry
