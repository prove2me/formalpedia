-- Prove2me | Theorems.Thm_SmoothBandit_Regret_theorem_2
-- name    : SmoothBandit.Regret.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:42:40.503193+00:00
-- url     : https://prove2.me/theorems/dd1fd717-3b2f-40aa-8694-53bbd928f0b0
-- title:
--   Theorem 2, p. 25 — SmoothBandit's regret is O(T^{(β+d−αβ)/(2β+d)} log^{1+d/(2β)} T + log² T) (αβ < β+d, or αβ > β+d with d ≤ 2β) and Õ(T^{(β+d−αβ)/(2β+d)} + 1), uniformly over the class
-- statement:
--   Fix the dimension $d \ge 1$ and parameters $\beta \ge 1$, $L, L_1 > 0$, $0 < c_0 \le 1$, $r_0 > 0$, $0 < \mu_{\min} \le \mu_{\max}$, $\gamma > 0$, $\alpha \ge 0$, and write
--
--   $$e = \frac{\beta + d - \alpha\beta}{2\beta + d}.$$
--
--   Let $R_T(\hat\pi)$ be the regret of Algorithm 1 (SmoothBandit) run with horizon $T$ on an instance of the class $\mathcal P(\beta, L_1, L, c_0, r_0, \mu_{\min}, \mu_{\max}, \gamma, \alpha)$ (Assumptions 1 to 4). Then:
--   1. if $\alpha\beta < \beta + d$, or if $d \le 2\beta$ and $\alpha\beta > \beta + d$, there are constants $C > 0$ and $T_0$, depending only on the parameters, such that for every $T \ge T_0$ and every instance of the class
--   $$R_T(\hat\pi) \le C\big(T^{e}\log^{1+\frac{d}{2\beta}}(T) + \log^2(T)\big);$$
--   2. for every $\alpha \ge 0$ there are constants $C > 0$, $T_0$ and an integer $m$, depending only on the parameters, such that for every $T \ge T_0$ and every instance of the class
--   $$R_T(\hat\pi) \le C\,(T^{e} + 1)\log^m(T).$$
--
--   That is, $R_T(\hat\pi) = O(T^e\log^{1+d/(2\beta)}T + \log^2 T) = \tilde O(T^e + 1)$ uniformly over the class. Combined with the paper's lower bound (Theorem 3) this is the minimax regret rate of smooth contextual bandits, interpolating between the non-differentiable rate ($\beta = 1$) and the parametric rate ($\beta \to \infty$).
--
--   **Formalization Note.** The constants come before the instance, which is what "the $O(\cdot)$ terms only depend on the parameters of Assumptions 1 to 4" asserts. The page writes $R_T(\pi)$ for $R_T(\hat\pi)$. Clause 1 carries the parameter restriction "$\alpha\beta < \beta + d$, or $d \le 2\beta$ and $\alpha\beta > \beta + d$": as printed the $O$-form fails for $\alpha\beta > \beta + d$ when $d > 2\beta$ (e.g. $\beta = 1$, $d = 3$, $\alpha = 5$): epoch 1 alone costs regret of order $\log^{1+d/(2\beta)}T$, which exceeds $\log^2 T$, while $T^e \to 0$. The explicit constant of the proof (p. 52) is valid only for $\alpha\beta < \beta + d$. For $d \le 2\beta$ and $\alpha\beta > \beta + d$ the first sum of display (13) is a convergent geometric series of size $O(\log^{1+d/(2\beta)}T + \log T) = O(\log^2 T)$, so the printed $O$-form holds there and is kept. The boundary case $\alpha\beta = \beta + d$, where the proof gives an extra factor $\log T$, is not claimed. Clause 2 is the printed $\tilde O(T^e + 1)$ for every $\alpha \ge 0$, with the logarithmic factor made explicit.
-- source:
--   Hu, Kallus & Mao, Smooth Contextual Bandits, arXiv:1909.02553v4, p. 25, Theorem 2 (proof pp. 51–52)

import Mathlib
import Definitions.Def_SmoothBandit_Regret_Algorithm

open MeasureTheory

namespace SmoothBandit.Regret

theorem theorem_2 (d : ℕ) (hd : 1 ≤ d) (P : Params) (hP : P.Standing) :
    (P.α * P.β < P.β + d ∨ ((d : ℝ) ≤ 2 * P.β ∧ P.β + d < P.α * P.β) →
      ∃ C T0 : ℝ, 0 < C ∧ ∀ T : ℕ, T0 ≤ T →
        ∀ (Ω : Type) [MeasurableSpace Ω] (M : Machine d Ω), InClass P M →
          regret P M T ≤
            C * ((T : ℝ) ^ ((P.β + d - P.α * P.β) / (2 * P.β + d)) *
                Real.log T ^ (1 + (d : ℝ) / (2 * P.β)) + Real.log T ^ 2)) ∧
    (∃ C T0 : ℝ, ∃ m : ℕ, 0 < C ∧ ∀ T : ℕ, T0 ≤ T →
        ∀ (Ω : Type) [MeasurableSpace Ω] (M : Machine d Ω), InClass P M →
          regret P M T ≤
            C * ((T : ℝ) ^ ((P.β + d - P.α * P.β) / (2 * P.β + d)) + 1) * Real.log T ^ m) := by sorry

end SmoothBandit.Regret
