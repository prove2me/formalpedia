-- Prove2me | Theorems.Thm_Rudin_ch03_root_test
-- name    : Rudin.ch03_root_test
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T19:10:51.515836+00:00
-- url     : https://prove2.me/theorems/27e54e7b-8662-440c-aaaa-546594ca0dd7
-- title:
--   Theorem 3.33 — root test
-- statement:
--   Put $\alpha = \limsup_n \|a_n\|^{1/n}$ in the extended reals. If $\alpha < 1$ then $\sum a_n$ converges; if $\alpha > 1$ then $\sum a_n$ diverges. (For $\alpha = 1$ no conclusion is possible, as Rudin's examples show.)
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 3, p. 65, Theorem 3.33

import Mathlib
import Definitions.Def_Rudin_ch03_series

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 3.33 (root test): put `α = limsup ‖aₙ‖^{1/n}` in the extended reals.  If
`α < 1` the series `∑ aₙ` converges; if `α > 1` it diverges. -/
theorem ch03_root_test (a : ℕ → ℂ) :
    (limsup (fun n => ((‖a n‖ ^ ((n : ℝ)⁻¹) : ℝ) : EReal)) atTop < 1 → SeriesConverges a) ∧
    (1 < limsup (fun n => ((‖a n‖ ^ ((n : ℝ)⁻¹) : ℝ) : EReal)) atTop →
      ¬ SeriesConverges a) := by sorry

end Rudin
