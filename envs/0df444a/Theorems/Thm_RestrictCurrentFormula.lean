-- Prove2me | Theorems.Thm_RestrictCurrentFormula
-- name    : RestrictCurrentFormula
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:51:36.925609+00:00
-- url     : https://prove2.me/theorems/384ee9db-b6ef-4afd-8a79-e711fb705334
-- title:
--   Restrict Current Formula: Restrict Current Formula
-- statement:
--   The current of a restriction, computed as the un-reparametrized integral over the original
--   domain: this is what lets `CurrentResolutionAdditive`'s un-reparametrized resolution sum be read as
--   a sum of currents of the restricted pieces.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/RestrictCurrentFormula.lean#L11-L55
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/RestrictCurrentFormula.lean#L11-L55

import Definitions.Def_Tablet_curveCurrent
import Definitions.Def_Tablet_curveRestrict
import Definitions.Def_Tablet_CurrentConcatAdditive
import Definitions.Def_Tablet_RestrictCurrentFormula
import Theorems.Thm_CurrentConcatAdditive

set_option autoImplicit false
open Set MeasureTheory

theorem RestrictCurrentFormula {E : Type*} [MetricSpace E] (γ : Curve E) (a b : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ γ.len) (ω : Form1 E) :
    curveCurrent (curveRestrict γ a b ha hab hb) ω
      = ∫ t in a..b, ω.f (γ.toFun t) * deriv (ω.pi ∘ γ.toFun) t := by sorry
