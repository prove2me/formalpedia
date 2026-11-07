-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_tensorPrime_isReduced_of_quotient
-- name    : QEC.Coding.AlgebraicGeometry.tensorPrime_isReduced_of_quotient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:33:27.782121+00:00
-- url     : https://prove2.me/theorems/3486deb1-a93d-4368-99af-c8f4c81d4dc6
-- title:
--   Algebraic Geometry: tensor Prime is Reduced of quotient
-- statement:
--   The Algebraic Geometry construction uses the tensor Prime is Reduced of quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalReducedSpecialFiber.lean#L37-L40
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalReducedSpecialFiber.lean#L37-L40

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalSpecialFiber
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFibreFrobenius
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReducedSpecialFiber
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
open scoped TensorProduct

theorem QEC.Coding.AlgebraicGeometry.tensorPrime_isReduced_of_quotient (C : Type) [CommRing C] (p : ℕ)
    [IsReduced (C ⧸ Ideal.span {(p : C)})] : IsReduced (C ⊗[ℤ] ZMod p) := by sorry
