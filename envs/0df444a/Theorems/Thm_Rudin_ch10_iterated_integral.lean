-- Prove2me | Theorems.Thm_Rudin_ch10_iterated_integral
-- name    : Rudin.ch10_iterated_integral
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-09-12T20:14:04.150994+00:00
-- url     : https://prove2.me/theorems/2abd43a8-8473-4edc-b9ec-502fb231b30d
-- title:
--   Theorem 10.2 — the order of integration is immaterial
-- statement:
--   For a continuous function on a 2-cell $[a,b]\times[c,d]$ the two iterated integrals agree: $\int_a^b\!\int_c^d f(x,y)\,dy\,dx = \int_c^d\!\int_a^b f(x,y)\,dx\,dy$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 10, p. 246, Definition 10.1 and Theorem 10.2

import Mathlib
import Definitions.Def_Rudin_ch10_forms

open Filter Topology MeasureTheory

namespace Rudin

/-- Rudin, Theorem 10.2: for a continuous function on a 2-cell the two iterated integrals agree;
the order of integration is immaterial. -/
theorem ch10_iterated_integral (a b c d : ℝ) (f : ℝ → ℝ → ℝ)
    (hf : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) (Set.Icc a b ×ˢ Set.Icc c d)) :
    (∫ x in a..b, ∫ y in c..d, f x y) = ∫ y in c..d, ∫ x in a..b, f x y := by sorry

end Rudin
