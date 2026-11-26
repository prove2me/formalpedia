-- Prove2me | Theorems.Thm_RestrictFullIsSelf
-- name    : RestrictFullIsSelf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:11:25.282471+00:00
-- url     : https://prove2.me/theorems/b9c6077a-d003-414e-950f-f2c145746a0c
-- title:
--   Restrict Full Is Self: Restrict Full Is Self
-- statement:
--   Restricting a curve `A` to its own full domain `[0, A.len]` recovers `A` itself.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/RestrictFullIsSelf.lean#L7-L18
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/RestrictFullIsSelf.lean#L7-L18

import Definitions.Def_Tablet_curveRestrict
import Definitions.Def_Tablet_RestrictFullIsSelf
set_option autoImplicit false
open Set

theorem RestrictFullIsSelf {E : Type*} [MetricSpace E] (A : Curve E) :
    curveRestrict A 0 A.len (le_refl 0) A.len_nonneg (le_refl A.len) = A := by sorry
