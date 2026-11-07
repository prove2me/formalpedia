-- Prove2me | Theorems.Thm_QEC_Coding_LocallyMinimalDistance_elementaryCoboundaryMoves_subset_firstCoboundaryCheckCode
-- name    : QEC.Coding.LocallyMinimalDistance.elementaryCoboundaryMoves_subset_firstCoboundaryCheckCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:17:55.449456+00:00
-- url     : https://prove2.me/theorems/d0672f2b-9d75-4480-b32f-ff1c8f203f71
-- title:
--   Locally Minimal Distance: elementary Coboundary Moves subset first Coboundary Check Code
-- statement:
--   Every elementary coboundary move belongs to the first coboundary code.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocallyMinimalDistance.lean#L148-L157
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocallyMinimalDistance.lean#L148-L157

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.Order.Lattice.Nat
import Definitions.Def_QEC_Coding_ExpanderCodes_LocallyMinimalDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.LocallyMinimalDistance
universe u v
variable {C : Type*} [AddCommGroup C]

theorem QEC.Coding.LocallyMinimalDistance.elementaryCoboundaryMoves_subset_firstCoboundaryCheckCode
    {F : Type u} {ι κ₀ κ₂ : Type v} [Field F] [Fintype F]
    [Fintype ι] [Fintype κ₀] [Fintype κ₂]
    (K : ChainComplexData F (Word F κ₀) (Word F ι) (Word F κ₂))
    (m : Word F ι) (hm : m ∈ elementaryCoboundaryMoves K) :
    m ∈ K.firstCoboundaryCheckCode.carrier := by sorry
