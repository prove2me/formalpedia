-- Prove2me | Theorems.Thm_QEC_Coding_SubsystemCSSData_dual_dressedXDistanceAtLeast_iff
-- name    : QEC.Coding.SubsystemCSSData.dual_dressedXDistanceAtLeast_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:41:34.265836+00:00
-- url     : https://prove2.me/theorems/479319dd-c55c-4fb3-b587-979ff0f12c06
-- title:
--   Subsystem CSSData: dual dressed XDistance At Least iff
-- statement:
--   The Subsystem CSSData construction uses the dual dressed XDistance At Least iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/SubsystemDual.lean#L130-L161
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/SubsystemDual.lean#L130-L161

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

theorem QEC.Coding.SubsystemCSSData.dual_dressedXDistanceAtLeast_iff
    (D : SubsystemCSSData i0 i1 i2 LogicalZ LogicalX) (d : Nat) :
    D.dual.DressedXDistanceAtLeast d ↔ D.DressedZDistanceAtLeast d := by sorry
