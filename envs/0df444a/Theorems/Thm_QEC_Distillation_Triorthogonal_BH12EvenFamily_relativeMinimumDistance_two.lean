-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12EvenFamily_relativeMinimumDistance_two
-- name    : QEC.Distillation.Triorthogonal.BH12EvenFamily.relativeMinimumDistance_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:06:04.424207+00:00
-- url     : https://prove2.me/theorems/c1c67444-9863-4434-9733-cc00d12a71a0
-- title:
--   BH12 Even Family: relative Minimum Distance two
-- statement:
--   For `q>0`, the pure-`Z` relative sector has exact minimum distance two.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/EvenFamily.lean#L681-L686
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/EvenFamily.lean#L681-L686

import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12EvenFamily
open Coding
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.Triorthogonal.BH12EvenFamily.relativeMinimumDistance_two {q : Nat} (hq : 0 < q) :
    RelativeMinimumDistance (family q).evenCode.dual (family q).rowCode.dual 2 := by sorry
