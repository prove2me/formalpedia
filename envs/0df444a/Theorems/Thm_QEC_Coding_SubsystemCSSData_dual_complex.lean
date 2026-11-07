-- Prove2me | Theorems.Thm_QEC_Coding_SubsystemCSSData_dual_complex
-- name    : QEC.Coding.SubsystemCSSData.dual_complex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:37:44.634209+00:00
-- url     : https://prove2.me/theorems/8e4c1548-0f1d-4aa8-8254-4c168fb42702
-- title:
--   Subsystem CSSData: dual complex
-- statement:
--   The Subsystem CSSData construction uses the dual complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/SubsystemDual.lean#L121-L123
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/SubsystemDual.lean#L121-L123

import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_CSS_Subsystem
import Definitions.Def_QEC_Coding_CSS_SubsystemDual
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SubsystemCSSData
universe u v
variable {i0 i1 i2 : Type u} {LogicalZ LogicalX : Type v}
variable [Fintype i0] [Fintype i1] [Fintype i2]
variable [AddCommGroup LogicalZ] [Module (ZMod 2) LogicalZ]
variable [AddCommGroup LogicalX] [Module (ZMod 2) LogicalX]
variable [Module.Finite (ZMod 2) LogicalZ]
variable [Module.Finite (ZMod 2) LogicalX]

theorem QEC.Coding.SubsystemCSSData.dual_complex
    (D : SubsystemCSSData i0 i1 i2 LogicalZ LogicalX) :
    D.dual.complex = dualChainComplex D.complex := by sorry

attribute [defeq] QEC.Coding.SubsystemCSSData.dual_complex
