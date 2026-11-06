-- Prove2me | Theorems.Thm_RH_Transport_continuationBoundary_eq_sub_margin
-- name    : RH.Transport.continuationBoundary_eq_sub_margin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:27:51.170659+00:00
-- url     : https://prove2.me/theorems/c4e972a9-c854-4275-8ff3-9a5c4c45c689
-- title:
--   Transport: continuation Boundary eq sub margin
-- statement:
--   The Transport construction uses the continuation Boundary eq sub margin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/Continuation.lean#L29-L35
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/Continuation.lean#L29-L35

import Definitions.Def_OAI_NumberTheory_DirichletL_Continuation
import Definitions.Def_Transport_Continuation
set_option autoImplicit false
open RH RH.Transport
noncomputable section
open Filter Asymptotics MeasureTheory
open OAI.SevenEighths.Continuation

theorem RH.Transport.continuationBoundary_eq_sub_margin (B β ω σ : ℝ) :
    continuationBoundary B β ω σ = β - continuationMargin B β ω σ := by sorry
