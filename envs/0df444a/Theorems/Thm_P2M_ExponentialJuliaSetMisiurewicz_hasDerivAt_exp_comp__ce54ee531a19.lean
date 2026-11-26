-- Prove2me | Theorems.Thm_P2M_ExponentialJuliaSetMisiurewicz_hasDerivAt_exp_comp__ce54ee531a19
-- name    : P2M_ExponentialJuliaSetMisiurewicz_hasDerivAt_exp_comp__ce54ee531a19
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:58:14.874799+00:00
-- url     : https://prove2.me/theorems/b1ed0e9c-97fe-4dc3-a8c4-0fa220ab24c5
-- title:
--   P2 M Exponential Julia Set Misiurewicz has Deriv At exp comp  ce54ee531a19: P2 M Exponential Julia Set Misiurewicz has Deriv At exp comp  ce54ee531a19
-- statement:
--   The exponential chain rule with the outer derivative written first.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Basic.lean#L96-L101
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Basic.lean#L96-L101

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Continuity
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Definitions.Def_ExpChaotic_Basic
set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section

theorem P2M_ExponentialJuliaSetMisiurewicz_hasDerivAt_exp_comp__ce54ee531a19
    {f : ℂ → ℂ} {f' z : ℂ}
    (hf : HasDerivAt f f' z) :
    HasDerivAt (Complex.exp ∘ f)
      (Complex.exp (f z) * f') z := by sorry

alias «ExponentialJuliaSetMisiurewicz».«hasDerivAt_exp_comp'» := P2M_ExponentialJuliaSetMisiurewicz_hasDerivAt_exp_comp__ce54ee531a19
