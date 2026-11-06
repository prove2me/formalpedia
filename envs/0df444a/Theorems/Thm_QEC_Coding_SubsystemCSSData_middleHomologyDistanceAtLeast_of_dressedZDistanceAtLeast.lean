-- Prove2me | Theorems.Thm_QEC_Coding_SubsystemCSSData_middleHomologyDistanceAtLeast_of_dressedZDistanceAtLeast
-- name    : QEC.Coding.SubsystemCSSData.middleHomologyDistanceAtLeast_of_dressedZDistanceAtLeast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:00:20.879197+00:00
-- url     : https://prove2.me/theorems/e192d2e0-4397-4b18-90dc-2b51c896e1fc
-- title:
--   Subsystem CSSData: middle Homology Distance At Least of dressed ZDistance At Least
-- statement:
--   If the homology projection is injective (in particular, for the identity
--   projection), dressed `Z` distance is exactly ordinary homological distance.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/Subsystem.lean#L118-L136
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/Subsystem.lean#L118-L136

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

theorem QEC.Coding.SubsystemCSSData.middleHomologyDistanceAtLeast_of_dressedZDistanceAtLeast
    (D : SubsystemCSSData i0 i1 i2 LogicalZ LogicalX) (d : Nat)
    (hInjective : Function.Injective D.homologyProjection)
    (h : D.DressedZDistanceAtLeast d) :
    MiddleHomologyDistanceAtLeast D.complex d := by sorry
