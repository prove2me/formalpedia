-- Prove2me | Theorems.Thm_QubitFreqSensing_fact_5_5
-- name    : QubitFreqSensing.fact_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:23:40.810729+00:00
-- url     : https://prove2.me/theorems/d84588f3-7542-4106-b18c-709214988caf
-- title:
--   Fact 5.5 — properties of the Möbius maps $L_{\pm,a}$
-- statement:
--   Let $|a|<1$ and $\varepsilon\in\{1,-1\}$, and let $L_{\varepsilon,a}(z)=(a+\varepsilon z)/(1+\varepsilon\bar a z)$. Then:
--
--   1. $L_{\varepsilon,a}$ is holomorphic on the unit disc $\mathbb D$, maps $\mathbb D$ into $\mathbb D$, and $L_{\varepsilon,a}(0)=a$;
--   2. $|L_{\varepsilon,a}(z)|\le1$ for all $|z|\le1$, with equality if and only if $|z|=1$;
--   3. wherever $1+\varepsilon\bar a z\ne0$ (in particular for $|z|\le1$),
--   $$
--   1-|L_{\varepsilon,a}(z)|^2=\frac{(1-|a|^2)(1-|z|^2)}{|1+\varepsilon\bar a z|^2};
--   $$
--   4. for $|z|<1$,
--   $$
--   L_{\varepsilon,a}(z)=a+(1-|a|^2)\sum_{\ell=1}^\infty\varepsilon^\ell(-\bar a)^{\ell-1}z^\ell .
--   $$
--
--   Bullet 3 computes the change of the penalty term of $J$ under $\Phi^{(i)}_z$ (Corollary 5.10), and bullet 4 gives the linear part of $z\mapsto\langle g_i,\Phi^{(i)}_z u\rangle$ (Lemma 5.9).
--
--   **Formalization Note** The series is a `HasSum` indexed by $n=\ell-1\ge0$.
--
--   Differences from the source:
--   - encoding: 1 − |L±,a(z)|² = (1 − |a|²)(1 − |z|²)/|1 ± āz|², stated without a domain → for every z with 1 + ε ā z ≠ 0; reason: at the pole both sides are undefined; the closed unit disc is inside the stated domain
--   - encoding: Σ_{ℓ=1}^∞ (±1)^ℓ(−ā)^{ℓ−1}z^ℓ → HasSum over n = ℓ − 1 ∈ ℕ; reason: index shift
-- source:
--   Chen, Coladangelo, Li, Zhang, Sensing frequencies at the discrete Grover-Heisenberg limit using a single qubit, manuscript (STOC 2027 submission; held version sha256 fd015276…c95c9a2), Fact 5.5, p.17 (PDF p.17)

import Mathlib
import Definitions.Def_QubitFreqSensing_Mobius

namespace QubitFreqSensing

/-- **Fact 5.5** (Chen, Coladangelo, Li, Zhang, manuscript (STOC 2027 submission), Fact 5.5, p.17).
"For all a satisfying |a| < 1, we have:
• L±,a is a holomorphic function mapping D to D satisfying L±,a(0) = a.
• |L±,a(z)| ≤ 1 for all |z| ≤ 1, with equality if and only if |z| = 1.
• We have: 1 − |L±,a(z)|² = (1 − |a|²)(1 − |z|²)/|1 ± āz|².
• L±,a has the following series expansion around z = 0, valid for all |z| < 1:
L±,a(z) = a + (1 − |a|²) Σ_{ℓ=1}^∞ (±1)^ℓ (−ā)^{ℓ−1} z^ℓ."

All four bullets, for both signs `ε = ±1` (`mob ε a = L_{ε,a}`).

**Formalization Note** The identity of bullet 3 is stated wherever both sides are defined,
`1 ± āz ≠ 0` (this includes the closed unit disc). The series of bullet 4 is a `HasSum` with the
summation index shifted, `ℓ = n + 1`. -/
theorem fact_5_5 (a : ℂ) (ha : ‖a‖ < 1) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    (DifferentiableOn ℂ (mob ε a) (Metric.ball 0 1) ∧
      Set.MapsTo (mob ε a) (Metric.ball 0 1) (Metric.ball 0 1) ∧ mob ε a 0 = a) ∧
    (∀ z : ℂ, ‖z‖ ≤ 1 → ‖mob ε a z‖ ≤ 1 ∧ (‖mob ε a z‖ = 1 ↔ ‖z‖ = 1)) ∧
    (∀ z : ℂ, 1 + (ε : ℂ) * (starRingEnd ℂ) a * z ≠ 0 →
      1 - ‖mob ε a z‖ ^ 2 =
        (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) / ‖1 + (ε : ℂ) * (starRingEnd ℂ) a * z‖ ^ 2) ∧
    (∀ z : ℂ, ‖z‖ < 1 →
      HasSum (fun n : ℕ => ((1 - ‖a‖ ^ 2 : ℝ) : ℂ) * (ε : ℂ) ^ (n + 1) *
          (-(starRingEnd ℂ) a) ^ n * z ^ (n + 1))
        (mob ε a z - a)) := by sorry

end QubitFreqSensing
