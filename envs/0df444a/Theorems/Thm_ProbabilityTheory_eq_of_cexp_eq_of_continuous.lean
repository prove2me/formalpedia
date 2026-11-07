-- Prove2me | Theorems.Thm_ProbabilityTheory_eq_of_cexp_eq_of_continuous
-- name    : ProbabilityTheory.eq_of_cexp_eq_of_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T23:43:20.280469+00:00
-- url     : https://prove2.me/theorems/eeb36cea-85d6-4315-87c4-554c10e06e6d
-- title:
--   Uniqueness of continuous complex logarithms on the real line
-- statement:
--   Two continuous complex-valued functions on the connected real line with equal exponentials and the same value at zero coincide everywhere.
-- source:
--   slink/LeanLevy commit 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/Levy/LevyKhintchineUniqueness.lean, source-private lemma eq_of_cexp_eq_of_continuous.

import Mathlib
open MeasureTheory ProbabilityTheory Filter Topology Complex

theorem ProbabilityTheory.eq_of_cexp_eq_of_continuous {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) (h0 : f 0 = g 0) (h : ∀ ξ, Complex.exp (f ξ) = Complex.exp (g ξ)) : f = g := by sorry
