-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12EvenFamily_evenWeight_in_logicalCount
-- name    : QEC.Distillation.Triorthogonal.BH12EvenFamily.evenWeight_in_logicalCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T21:35:56.089295+00:00
-- url     : https://prove2.me/theorems/d38b656e-77ef-410b-a2de-00c181632da1
-- title:
--   BH12 Even Family: even Weight in logical Count
-- statement:
--   The BH12 Even Family construction uses the even Weight in logical Count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/EvenFamily.lean#L270-L274
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/EvenFamily.lean#L270-L274

import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12EvenFamily
open Coding
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.Triorthogonal.BH12EvenFamily.evenWeight_in_logicalCount {q : Nat} (r : EvenRow) :
    HammingWeight (evenWord (q := q) r) =
      ![4 + 2 * logicalCount q, 4 + 2 * logicalCount q, 8] r := by sorry
