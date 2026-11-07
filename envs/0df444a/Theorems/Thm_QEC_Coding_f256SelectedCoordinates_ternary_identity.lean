-- Prove2me | Theorems.Thm_QEC_Coding_f256SelectedCoordinates_ternary_identity
-- name    : QEC.Coding.f256SelectedCoordinates_ternary_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:49:49.615374+00:00
-- url     : https://prove2.me/theorems/823b336f-46d3-4bd6-b7c2-ba54c129ff82
-- title:
--   Coding: f256 Selected Coordinates ternary identity
-- statement:
--   The Coding construction uses the f256 Selected Coordinates ternary identity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteFieldMultiplication/BinaryConversion.lean#L56-L64
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteFieldMultiplication/BinaryConversion.lean#L56-L64

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_Selector
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_BinaryConversion
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
open scoped BigOperators

theorem QEC.Coding.f256SelectedCoordinates_ternary_identity (x y z : F256) :
    (∑ q ∈ f256SelectedCoordinates,
      f256MFESigma x q * f256MFESigma y (f256MFEpi2 q) *
        f256MFESigma z (f256MFEpi3 q)) = f256RMFEpsi (x * y * z) := by sorry
