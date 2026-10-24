-- Prove2me | Theorems.Thm_PersonalizedAssortment_IB_riemann_sum_bound
-- name    : PersonalizedAssortment.IB.riemann_sum_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T01:45:05.029043+00:00
-- url     : https://prove2.me/theorems/058d13ab-27ae-44c3-bf6e-c1f08b91b128
-- title:
--   Riemann-sum bound: $\frac1c\sum_{k=I+1}^{c}\Psi(k/c)\le\frac1c+\int_{(I+1)/c}^1\Psi$
-- statement:
--   Let $\Psi$ be a penalty function ($\Psi:[0,1]\to[0,1]$ increasing, $\Psi(0)=0$, $\Psi(1)=1$). Let $c$ be a positive integer and $I$ an integer with $0\le I<c$. Then
--   $$\frac1c\sum_{k=I+1}^{c}\Psi\!\left(\frac kc\right)\;\le\;\frac1c+\int_{(I+1)/c}^{1}\Psi(y)\,dy .$$
--
--   In the proof of Theorem 1, $I$ is the final inventory $I_i^T$ of a product with initial inventory $c=c_i$. The bound turns the discrete dual value of that product into the continuous expression that appears in $\alpha_{c_{\min}}(\Psi)$.
-- source:
--   Golrezaei, Nazerzadeh, Rusmevichientong, Real-Time Optimization of Personalized Assortments, Management Sci. 60(6), 2014, https://doi.org/10.1287/mnsc.2014.1939, p. 1549, Section A.3, proof of Theorem 1, display after 'Because Psi(1) = 1 and Psi is increasing, we have'

import Mathlib
import Definitions.Def_PersonalizedAssortment_IB_PenaltyFunction

namespace PersonalizedAssortment.IB

/-- §A.3, p. 1549: for a penalty function `Ψ`, a positive integer `c` and an integer `0 ≤ I < c`,
`(1/c) ∑_{k=I+1}^{c} Ψ(k/c) ≤ 1/c + ∫_{(I+1)/c}^1 Ψ(y) dy`. -/
theorem riemann_sum_bound (Ψ : ℝ → ℝ) (hΨ : IsPenaltyFunction Ψ) (c : ℕ) (hc : 0 < c)
    (I : ℕ) (hI : I < c) :
    1 / (c : ℝ) * ∑ k ∈ Finset.Ioc I c, Ψ ((k : ℝ) / (c : ℝ)) ≤
      1 / (c : ℝ) + ∫ y in ((I : ℝ) + 1) / (c : ℝ)..1, Ψ y := by sorry

end PersonalizedAssortment.IB
