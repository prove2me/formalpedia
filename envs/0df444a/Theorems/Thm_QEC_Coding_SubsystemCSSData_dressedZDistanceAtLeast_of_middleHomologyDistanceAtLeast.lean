-- Prove2me | Theorems.Thm_QEC_Coding_SubsystemCSSData_dressedZDistanceAtLeast_of_middleHomologyDistanceAtLeast
-- name    : QEC.Coding.SubsystemCSSData.dressedZDistanceAtLeast_of_middleHomologyDistanceAtLeast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:59:37.044023+00:00
-- url     : https://prove2.me/theorems/b13c082e-6851-435f-b4c4-d82d24c4e13a
-- title:
--   Subsystem CSSData: dressed ZDistance At Least of middle Homology Distance At Least
-- statement:
--   Ordinary homological distance implies dressed `Z` distance for every quotient sector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/Subsystem.lean#L98-L112
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/Subsystem.lean#L98-L112

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

theorem QEC.Coding.SubsystemCSSData.dressedZDistanceAtLeast_of_middleHomologyDistanceAtLeast
    (D : SubsystemCSSData i0 i1 i2 LogicalZ LogicalX) (d : Nat)
    (h : MiddleHomologyDistanceAtLeast D.complex d) :
    D.DressedZDistanceAtLeast d := by sorry
