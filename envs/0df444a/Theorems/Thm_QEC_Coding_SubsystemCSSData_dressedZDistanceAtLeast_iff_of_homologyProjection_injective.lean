-- Prove2me | Theorems.Thm_QEC_Coding_SubsystemCSSData_dressedZDistanceAtLeast_iff_of_homologyProjection_injective
-- name    : QEC.Coding.SubsystemCSSData.dressedZDistanceAtLeast_iff_of_homologyProjection_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:36:36.3688+00:00
-- url     : https://prove2.me/theorems/d133cf0b-1293-498e-a246-63a8e158a2d0
-- title:
--   Subsystem CSSData: dressed ZDistance At Least iff of homology Projection injective
-- statement:
--   The Subsystem CSSData construction uses the dressed ZDistance At Least iff of homology Projection injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/Subsystem.lean#L138-L145
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/Subsystem.lean#L138-L145

import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_CSS_Subsystem
set_option autoImplicit false
open QEC QEC.Coding
universe u v
open QEC.Coding.SubsystemCSSData
variable {i0 i1 i2 : Type u} {LogicalZ LogicalX : Type v}
variable [Fintype i0] [Fintype i1] [Fintype i2]
variable [AddCommGroup LogicalZ] [Module (ZMod 2) LogicalZ]
variable [AddCommGroup LogicalX] [Module (ZMod 2) LogicalX]
variable [Module.Finite (ZMod 2) LogicalZ] [Module.Finite (ZMod 2) LogicalX]

theorem QEC.Coding.SubsystemCSSData.dressedZDistanceAtLeast_iff_of_homologyProjection_injective
    (D : SubsystemCSSData i0 i1 i2 LogicalZ LogicalX) (d : Nat)
    (hInjective : Function.Injective D.homologyProjection) :
    D.DressedZDistanceAtLeast d ↔
      MiddleHomologyDistanceAtLeast D.complex d := by sorry
