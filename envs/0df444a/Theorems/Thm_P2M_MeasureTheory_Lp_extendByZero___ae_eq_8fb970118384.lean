-- Prove2me | Theorems.Thm_P2M_MeasureTheory_Lp_extendByZero___ae_eq_8fb970118384
-- name    : P2M_MeasureTheory_Lp_extendByZero___ae_eq_8fb970118384
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:40:54.006327+00:00
-- url     : https://prove2.me/theorems/6b76adb2-9cdf-4414-a459-98e37f9d745d
-- title:
--   P2 M Measure Theory Lp extend By Zero   ae eq 8fb970118384: P2 M Measure Theory Lp extend By Zero   ae eq 8fb970118384
-- statement:
--   The P2 M Measure Theory Lp extend By Zero   ae eq 8fb970118384 construction uses the P2 M Measure Theory Lp extend By Zero   ae eq 8fb970118384 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/rellich-kondrachov-lean4341.patch#L190-L195
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/rellich-kondrachov-lean4341.patch#L190-L195

import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Definitions.Def_RellichKondrachov_MeasureTheory_Function_LpSpace_Restrict
set_option autoImplicit true
open MeasureTheory
open scoped ENNReal
open MeasureTheory.Lp
noncomputable section
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {s : Set α} (hs : MeasurableSet s)

theorem P2M_MeasureTheory_Lp_extendByZero___ae_eq_8fb970118384 (f : Lp E p (μ.restrict s)) :
    ((extendByZeroₗᵢ (μ := μ) (p := p) (s := s) hs) f : α → E) =ᵐ[μ]
      s.indicator fun x : α => f x := by sorry

alias «MeasureTheory».«Lp».«extendByZeroₗᵢ_ae_eq» := P2M_MeasureTheory_Lp_extendByZero___ae_eq_8fb970118384
