-- Prove2me | Theorems.Thm_QEC_Coding_LinearCode_dual_dual_eq
-- name    : QEC.Coding.LinearCode.dual_dual_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:40:27.399126+00:00
-- url     : https://prove2.me/theorems/2ed5cf36-d9e2-48fb-8db7-c8ff3aaccdf2
-- title:
--   Linear Code: dual dual eq
-- statement:
--   The same involution at the code level.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Core/Duality.lean#L40-L41
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Core/Duality.lean#L40-L41

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Coding_Core_Duality
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.LinearCode
universe u v
variable {F : Type u} {ι : Type v} [Field F] [Fintype F] [Fintype ι]

theorem QEC.Coding.LinearCode.dual_dual_eq (C : LinearCode F ι) : C.dual.dual = C := by sorry
