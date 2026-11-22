-- Prove2me | Theorems.Thm_P2M_NemytskiiLebesgue_eLpNorm__norm_rpow_div_eq_f26ae8339226
-- name    : P2M_NemytskiiLebesgue_eLpNorm__norm_rpow_div_eq_f26ae8339226
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:35:00.08764+00:00
-- url     : https://prove2.me/theorems/18a816d2-0d7e-496c-ad0e-d9f93e305856
-- title:
--   P2 M Nemytskii Lebesgue e Lp Norm  norm rpow div eq f26ae8339226: P2 M Nemytskii Lebesgue e Lp Norm  norm rpow div eq f26ae8339226
-- statement:
--   The P2 M Nemytskii Lebesgue e Lp Norm  norm rpow div eq f26ae8339226 construction uses the P2 M Nemytskii Lebesgue e Lp Norm  norm rpow div eq f26ae8339226 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Basic.lean#L171-L176
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Basic.lean#L171-L176

module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic.Cases
public import Mathlib.Tactic.Have
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Basic
set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory
open scoped ENNReal
open scoped ENNReal
open scoped RealInnerProductSpace
open MeasureTheory

theorem P2M_NemytskiiLebesgue_eLpNorm__norm_rpow_div_eq_f26ae8339226
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [NormedAddCommGroup D] (u : Ω → D)
    {p α : ℝ} (hα : 0 < α) :
    eLpNorm' (‖u ·‖ ^ α) (p / α) μ = (eLpNorm' u p μ) ^ α := by sorry

alias «NemytskiiLebesgue».«eLpNorm'_norm_rpow_div_eq» := P2M_NemytskiiLebesgue_eLpNorm__norm_rpow_div_eq_f26ae8339226
