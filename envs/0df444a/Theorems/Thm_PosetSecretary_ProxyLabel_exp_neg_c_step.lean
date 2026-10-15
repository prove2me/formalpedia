-- Prove2me | Theorems.Thm_PosetSecretary_ProxyLabel_exp_neg_c_step
-- name    : PosetSecretary.ProxyLabel.exp_neg_c_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:48:33.876121+00:00
-- url     : https://prove2.me/theorems/f3067450-c099-4781-99af-7e4420173461
-- title:
--   Proof of Proposition 5.2, p. 17, second display (last inequality) — if ω/c ≤ ω′, c ≥ 1, then (1/(ω′+1))(1 − 1/(ω′+1))^ω ≥ 1/(e^c(ω′+1))
-- statement:
--   Let $\omega, \omega' \in \mathbb N$ and $c \ge 1$ be real with $\omega / c \le \omega'$. Then
--
--   $$\frac{1}{\omega'+1}\Big(1 - \frac{1}{\omega'+1}\Big)^{\omega} \ \ge\ \frac{1}{e^{c}(\omega'+1)} .$$
--
--   This is the last inequality of the second display in the proof of Proposition 5.2: it turns the selection bound (3), which involves the true width $\omega$, into a bound in terms of the width estimate $\omega'$ and the accuracy parameter $c$.
--
--   **Formalization Note** The exponent $\omega$ is a natural number. When $\omega' = 0$ the hypothesis forces $\omega = 0$, and the left side is $1$.
-- source:
--   Salem & Gupta, Secretary Problems with Biased Evaluations Using Partial Ordinal Information, SSRN 3444283 (version of 2022-04-17), proof of Proposition 5.2, p. 17, second display, last inequality

import Mathlib

namespace PosetSecretary.ProxyLabel

/-- Proof of Proposition 5.2, p. 17, second display, last inequality (Salem & Gupta,
SSRN 3444283): if `ω/c ≤ ω′` with `c ≥ 1`, then
`(1/(ω′+1)) (1 - 1/(ω′+1))^ω ≥ 1/(e^c (ω′+1))`. -/
theorem exp_neg_c_step (ω ω' : ℕ) (c : ℝ) (hc : 1 ≤ c) (hω' : (ω : ℝ) / c ≤ ω') :
    1 / (Real.exp c * (ω' + 1)) ≤ (1 / (ω' + 1 : ℝ)) * (1 - 1 / (ω' + 1 : ℝ)) ^ ω := by sorry

end PosetSecretary.ProxyLabel
