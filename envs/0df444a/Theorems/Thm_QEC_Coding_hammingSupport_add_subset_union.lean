-- Prove2me | Theorems.Thm_QEC_Coding_hammingSupport_add_subset_union
-- name    : QEC.Coding.hammingSupport_add_subset_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:32:35.895398+00:00
-- url     : https://prove2.me/theorems/d5e3e148-152c-4a19-92a7-b8a978c33041
-- title:
--   Coding: hamming Support add subset union
-- statement:
--   The Coding construction uses the hamming Support add subset union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Core/Definitions.lean#L265-L275
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Core/Definitions.lean#L265-L275

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Coding_Core_Definitions
set_option autoImplicit false
open QEC
open QEC.Coding
universe u v w x

theorem QEC.Coding.hammingSupport_add_subset_union {F : Type u} {ι : Type v}
    [AddGroup F] [DecidableEq F] [DecidableEq ι] [Fintype ι] (x y : Word F ι) :
    hammingSupport (x + y) ⊆ hammingSupport x ∪ hammingSupport y := by sorry
