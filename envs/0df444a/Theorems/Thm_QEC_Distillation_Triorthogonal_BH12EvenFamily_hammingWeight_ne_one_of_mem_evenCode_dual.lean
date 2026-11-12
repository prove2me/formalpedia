-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12EvenFamily_hammingWeight_ne_one_of_mem_evenCode_dual
-- name    : QEC.Distillation.Triorthogonal.BH12EvenFamily.hammingWeight_ne_one_of_mem_evenCode_dual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:05:31.38254+00:00
-- url     : https://prove2.me/theorems/abf4eec1-545b-4663-bff5-8527d1e26e8d
-- title:
--   BH12 Even Family: hamming Weight ne one of mem even Code dual
-- statement:
--   No word of weight one is orthogonal to every bottom row.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/EvenFamily.lean#L617-L628
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/EvenFamily.lean#L617-L628

import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12EvenFamily
open Coding
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.Triorthogonal.BH12EvenFamily.hammingWeight_ne_one_of_mem_evenCode_dual {q : Nat}
    {x : Word (ZMod 2) (Column q)} (hx : x ∈ (family q).evenCode.dual.carrier) :
    HammingWeight x ≠ 1 := by sorry
