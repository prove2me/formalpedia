-- Prove2me | Theorems.Thm_OrdinalMSP_Forbidden_integral_eval
-- name    : OrdinalMSP.Forbidden.integral_eval
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:18:55.667726+00:00
-- url     : https://prove2.me/theorems/92910d77-c1c8-4836-804f-b340f9558c55
-- title:
--   Proof of Lemma 1, p. 10 — ∫_p^1 (p/τ)^k dτ = −p ln(p) for k = 1 and (p − p^k)/(k − 1) for k ≥ 2
-- statement:
--   Let $0 < p \le 1$. Then
--   $$\int_p^1 \left(\frac{p}{\tau}\right)^k d\tau = \begin{cases} -p \ln(p), & k = 1,\\[4pt] \dfrac{p - p^k}{k-1}, & k \ge 2.\end{cases}$$
--
--   Combined with display (5) and the game bound, this gives the bound $\Pr(r^* \in \mathrm{ALG}) \ge -p\ln p$ (for $k = 1$) or $(p - p^k)/(k-1)$ (for $k \ge 2$) for every $r^* \in \mathrm{OPT}$, which is then optimized over $p$.
--
--   **Formalization Note** The statement is a conjunction: the case $k = 1$ (with the integrand written $(p/\tau)^1$) and, for every natural number $k \ge 2$, the closed form. `Real.log` is the natural logarithm; the interval integral is over $[p,1]$.
-- source:
--   Soto, Turkieltaub & Verdugo, Strong Algorithms for the Ordinal Matroid Secretary Problem, arXiv:1802.01997v1, proof of Lemma 1, p. 10, display following "We conclude that for every r∗ ∈ OPT,"

import Mathlib

namespace OrdinalMSP.Forbidden

theorem integral_eval (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    (∫ τ in p..1, (p / τ) ^ 1) = -p * Real.log p ∧
      ∀ k : ℕ, 2 ≤ k → (∫ τ in p..1, (p / τ) ^ k) = (p - p ^ k) / ((k : ℝ) - 1) := by sorry

end OrdinalMSP.Forbidden
