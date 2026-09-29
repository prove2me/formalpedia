-- Prove2me | Theorems.Thm_VapnikChervonenkis_GrowthFunction_phi_le_pow_add_one
-- name    : VapnikChervonenkis.GrowthFunction.phi_le_pow_add_one
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T19:35:36.136208+00:00
-- url     : https://prove2.me/theorems/7502aa84-5b51-4fc7-ba33-c427c9088084
-- title:
--   Φ(n, r) ≤ r^n + 1 for n > 0
-- statement:
--   Let $\Phi(n, r)$ be defined by the recurrence (1). For every $n > 0$ and every $r \ge 0$,
--
--   $$
--   \Phi(n, r) \le r^n + 1 .
--   $$
--
--   This bound turns the combinatorial estimate $m^S(r) \le \Phi(n, r)$ into the polynomial bound of Theorem 1.
--
--   **Formalization Note.** The inequality is non-strict, as stated on p. 266. The last sentence of the proof of Theorem 1 (p. 268) writes the strict form "for $r > 0$, $\Phi(n, r) < r^n + 1$", which is false at $n = r = 1$ ($\Phi(1,1) = 2 = 1^1 + 1$); Theorem 1 needs only the non-strict form. At $r = 0$ the bound reads $1 \le 0^n + 1 = 1$.
-- source:
--   Vapnik and Chervonenkis, On the Uniform Convergence of Relative Frequencies of Events to Their Probabilities, Theory Probab. Appl. 16 (1971), p. 266, sentence after the closed form of Φ(n, r)

import Mathlib
import Definitions.Def_VapnikChervonenkis_Shared_Phi

namespace VapnikChervonenkis.GrowthFunction

/-- Vapnik and Chervonenkis (1971), p. 266: "For `n > 0` and `r ≧ 0`, `Φ(n, r) ≦ r^n + 1`." -/
theorem phi_le_pow_add_one (n r : ℕ) (hn : 0 < n) :
    Shared.Phi n r ≤ r ^ n + 1 := by sorry

end VapnikChervonenkis.GrowthFunction
