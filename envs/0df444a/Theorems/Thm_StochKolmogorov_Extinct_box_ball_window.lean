-- Prove2me | Theorems.Thm_StochKolmogorov_Extinct_box_ball_window
-- name    : StochKolmogorov.Extinct.box_ball_window
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-03T19:43:40.536948+00:00
-- url     : https://prove2.me/theorems/55bb5d47-81a3-4d7e-a5a1-e03f6b0e36a3
-- title:
--   Every ball is reached from a box of the open orthant with positive probability in a short time window
-- statement:
--   Let $X^x$ be the family of solutions of the stochastic Kolmogorov system (1.1), $dX_i=X_if_i(X)\,dt+X_ig_i(X)\,dE_i(t)$, under Assumption 1.1, and write $P_T(x,\cdot)$ for the law of $X^x(T)$. For $0<\alpha\le\beta$, every $z$ in the box $[\alpha,\beta]^n$ and every $r>0$ there are $T_0>0$ and $p>0$ such that
--
--   $$P_T\big(y,B(z,r)\big)\ge p\qquad\text{for all } T\in[T_0/2,T_0]\text{ and all } y\in[\alpha,\beta]^n.$$
--
--   Role: the irreducibility input of the extinction theorem: from a compact box of the open orthant the process reaches every small ball around a point of the box with a uniform positive probability, which replaces the recurrence/transience dichotomy in the proof of Theorem 5.1.
-- source:
--   A. Hening, D. H. Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, https://arxiv.org/abs/1704.06984, proof of Theorem 5.1, p. 24 (the step after (5.15): entering a compact set K and (5.16)), with the nondegeneracy of Assumption 1.1; cf. the support theorem, D. W. Stroock, S. R. S. Varadhan, On the support of diffusion processes with applications to the strong maximum principle, Proc. Sixth Berkeley Symp. Math. Statist. Prob. 3 (1972) 333-359

import Mathlib
import Definitions.Def_StochKolmogorov_Extinct_Model
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Extinct

open EthierKurtz

theorem box_ball_window {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (hX : IsSolutionFamily P C B X)
    (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (α β : ℝ) (hα : 0 < α) (hαβ : α ≤ β) (z : SDEState n) (hz : ∀ l, α ≤ z l ∧ z l ≤ β)
    (r : ℝ) (hr : 0 < r) :
    ∃ T₀ : ℝ≥0, 0 < T₀ ∧ ∃ p : ℝ, 0 < p ∧ ∀ T : ℝ≥0, T₀ / 2 ≤ T → T ≤ T₀ →
      ∀ y : SDEState n, (∀ l, α ≤ y l ∧ y l ≤ β) →
        p ≤ (trans P X T y (Metric.ball z r)).toReal := by sorry

end StochKolmogorov.Extinct
