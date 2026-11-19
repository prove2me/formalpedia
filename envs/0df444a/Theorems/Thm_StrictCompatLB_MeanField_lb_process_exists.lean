-- Prove2me | Theorems.Thm_StrictCompatLB_MeanField_lb_process_exists
-- name    : StrictCompatLB.MeanField.lb_process_exists
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-18T08:30:10.744441+00:00
-- url     : https://prove2.me/theorems/4031129b-5839-46c8-a891-9c852ac49a48
-- title:
--   The load-balancing process exists from every initial state
-- statement:
--   Let $\lambda>0$, $N\ge 1$ and let route be a routing rule whose load-balancing kernel lbKernel is a stochastic kernel (nonnegative entries, rows summing to 1). Then for every initial state $z_0$ there is a probability space carrying a jump chain $Y$ and event clocks $\tau$ forming the load-balancing process IsLBProcess started from $z_0$.
--
--   Role: provides the processes started from each state to which the steady-state averaging is applied.
-- source:
--   D. Rutten, D. Mukherjee, Load Balancing Under Strict Compatibility Constraints, https://arxiv.org/abs/2008.07562, Section 2 (model), p. 8-9, constructed as the uniformized Markov chain of Appendix H, p. 46

import Mathlib
import Definitions.Def_StrictCompatLB_MeanField_Model

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace StrictCompatLB.MeanField

theorem lb_process_exists : ∀ (lam : ℝ), 0 < lam → ∀ (M : ℕ → ℕ) (N : ℕ), 1 ≤ N →
  ∀ (route : Fin (M N) → (Fin N → ℕ) → Fin N → ℝ),
    (∀ z, HasSum (lbKernel lam M N route z) 1) → (∀ z z', 0 ≤ lbKernel lam M N route z z') →
    ∀ z₀ : Fin N → ℕ, ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (Y : ℕ → Ω → (Fin N → ℕ)) (τ : ℕ → Ω → ℝ),
      IsLBProcess P lam M N route z₀ Y τ := by sorry

end StrictCompatLB.MeanField
