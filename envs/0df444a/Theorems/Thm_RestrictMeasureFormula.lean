-- Prove2me | Theorems.Thm_RestrictMeasureFormula
-- name    : RestrictMeasureFormula
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:11:38.19346+00:00
-- url     : https://prove2.me/theorems/5c58d94b-b5f9-4190-a347-7e359243e127
-- title:
--   Restrict Measure Formula: Restrict Measure Formula
-- statement:
--   The measure of a restriction, as the pushforward of Lebesgue measure restricted to the
--   original (un-shifted) subinterval `[a,b]`: this is the identification `MorreyResolutionAdditive`'s
--   Type I / Type III Morrey bound (`CutTypeI`'s Branch C) needs to splice the restricted block back
--   into a decomposition indexed on `γ`'s own parameter interval.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/RestrictMeasureFormula.lean#L12-L43
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/RestrictMeasureFormula.lean#L12-L43

import Definitions.Def_Tablet_curveMeasure
import Definitions.Def_Tablet_curveRestrict
import Definitions.Def_Tablet_CurveLipschitz
import Definitions.Def_Tablet_RestrictMeasureFormula
import Theorems.Thm_CurveLipschitz

set_option autoImplicit false
open MeasureTheory Set

theorem RestrictMeasureFormula {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (γ : Curve E) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ γ.len) :
    curveMeasure (curveRestrict γ a b ha hab hb)
      = Measure.map γ.toFun (volume.restrict (Set.Icc a b)) := by sorry
