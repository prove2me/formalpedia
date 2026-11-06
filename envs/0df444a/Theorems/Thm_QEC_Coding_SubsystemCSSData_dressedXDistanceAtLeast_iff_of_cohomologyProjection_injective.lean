-- Prove2me | Theorems.Thm_QEC_Coding_SubsystemCSSData_dressedXDistanceAtLeast_iff_of_cohomologyProjection_injective
-- name    : QEC.Coding.SubsystemCSSData.dressedXDistanceAtLeast_iff_of_cohomologyProjection_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:36:46.312619+00:00
-- url     : https://prove2.me/theorems/fd8fb59c-368e-467f-a93f-e445d9c6fbcf
-- title:
--   Subsystem CSSData: dressed XDistance At Least iff of cohomology Projection injective
-- statement:
--   The Subsystem CSSData construction uses the dressed XDistance At Least iff of cohomology Projection injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/Subsystem.lean#L185-L192
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/Subsystem.lean#L185-L192

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

theorem QEC.Coding.SubsystemCSSData.dressedXDistanceAtLeast_iff_of_cohomologyProjection_injective
    (D : SubsystemCSSData i0 i1 i2 LogicalZ LogicalX) (d : Nat)
    (hInjective : Function.Injective D.cohomologyProjection) :
    D.DressedXDistanceAtLeast d ↔
      MiddleCohomologyDistanceAtLeast D.complex d := by sorry
