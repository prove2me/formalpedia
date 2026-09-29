-- Prove2me | Theorems.Thm_Rudin_ch11_riemann_implies_lebesgue
-- name    : Rudin.ch11_riemann_implies_lebesgue
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T02:36:45.023894+00:00
-- url     : https://prove2.me/theorems/75082303-6be7-4f69-9369-5ee314b48371
-- title:
--   Theorem 11.33(a) — Riemann integrability implies Lebesgue integrability
-- statement:
--   If $f$ is Riemann-integrable on $[a, b]$ then $f$ is Lebesgue-integrable there and the two integrals have the same value.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 11, p. 323, Theorem 11.33(a)

import Mathlib
import Definitions.Def_Rudin_ch06_stieltjes
import Definitions.Def_Rudin_ch11_L2

open Filter Topology MeasureTheory

namespace Rudin

/-- Rudin, Theorem 11.33(a): a function that is Riemann-integrable on `[a, b]` is
Lebesgue-integrable there, and the two integrals agree. -/
theorem ch11_riemann_implies_lebesgue (a b : ℝ) (hab : a ≤ b) (f : ℝ → ℝ)
    (hf : RiemannIntegrable a b f) (hbdd : ∃ M, ∀ x ∈ Set.Icc a b, |f x| ≤ M) :
    IntegrableOn f (Set.Icc a b) volume ∧
      (∫ x in a..b, f x) = RiemannIntegral a b f := by sorry

end Rudin
