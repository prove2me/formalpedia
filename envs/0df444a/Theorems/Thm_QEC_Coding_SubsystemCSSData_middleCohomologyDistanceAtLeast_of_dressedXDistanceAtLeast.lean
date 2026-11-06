-- Prove2me | Theorems.Thm_QEC_Coding_SubsystemCSSData_middleCohomologyDistanceAtLeast_of_dressedXDistanceAtLeast
-- name    : QEC.Coding.SubsystemCSSData.middleCohomologyDistanceAtLeast_of_dressedXDistanceAtLeast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:00:31.342198+00:00
-- url     : https://prove2.me/theorems/a6924155-b35e-426b-84f0-cf707feca647
-- title:
--   Subsystem CSSData: middle Cohomology Distance At Least of dressed XDistance At Least
-- statement:
--   Identity-projection adapter for the cohomological sector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/Subsystem.lean#L165-L183
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/Subsystem.lean#L165-L183

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

theorem QEC.Coding.SubsystemCSSData.middleCohomologyDistanceAtLeast_of_dressedXDistanceAtLeast
    (D : SubsystemCSSData i0 i1 i2 LogicalZ LogicalX) (d : Nat)
    (hInjective : Function.Injective D.cohomologyProjection)
    (h : D.DressedXDistanceAtLeast d) :
    MiddleCohomologyDistanceAtLeast D.complex d := by sorry
