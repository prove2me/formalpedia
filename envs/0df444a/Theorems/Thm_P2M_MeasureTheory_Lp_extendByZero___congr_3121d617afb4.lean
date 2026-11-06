-- Prove2me | Theorems.Thm_P2M_MeasureTheory_Lp_extendByZero___congr_3121d617afb4
-- name    : P2M_MeasureTheory_Lp_extendByZero___congr_3121d617afb4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:38:03.736822+00:00
-- url     : https://prove2.me/theorems/aedf547b-7482-458d-bf72-c1374e1dde17
-- title:
--   P2 M Measure Theory Lp extend By Zero   congr 3121d617afb4: P2 M Measure Theory Lp extend By Zero   congr 3121d617afb4
-- statement:
--   The P2 M Measure Theory Lp extend By Zero   congr 3121d617afb4 construction uses the P2 M Measure Theory Lp extend By Zero   congr 3121d617afb4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/rellich-kondrachov-lean4341.patch#L197-L213
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/rellich-kondrachov-lean4341.patch#L197-L213

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

theorem P2M_MeasureTheory_Lp_extendByZero___congr_3121d617afb4 (hs₁ hs₂ : MeasurableSet s) :
    extendByZeroₗᵢ (μ := μ) (E := E) (p := p) (s := s) hs₁ =
      extendByZeroₗᵢ (μ := μ) (E := E) (p := p) (s := s) hs₂ := by sorry

alias «MeasureTheory».«Lp».«extendByZeroₗᵢ_congr» := P2M_MeasureTheory_Lp_extendByZero___congr_3121d617afb4
