-- Prove2me | Theorems.Thm_RandomListsMatching_GeneralRates_claim4_R_lower_bound
-- name    : RandomListsMatching.GeneralRates.claim4_R_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:08:35.171608+00:00
-- url     : https://prove2.me/theorems/e13f70b3-a0e2-454c-8c53-348f2696926a
-- title:
--   Claim 4, p. 16 (corrected to the limit f − s ≤ 1 − ln 2) — R(f, β, s) ≥ 0.706
-- statement:
--   Let $R$ be the function of p. 15,
--   $$
--   R(f,\beta,s) = \frac1f\Bigl(1 - e^{-f} + \frac1e\,\frac{s}{\beta}\,g(f,\beta) - \frac1{2e}\bigl(e^{-1}(s-\beta) + g(1,\beta)\bigr)^2 + \frac1{2e}\,g(f,\beta)^2\Bigr),
--   $$
--   with $g$ the function of Claim 2. If
--   $$
--   1 \ge f \ge s \ge \beta > 0 \quad\text{and}\quad f - s \le 1 - \ln 2,
--   $$
--   then
--   $$
--   R(f, \beta, s) \ge 0.706 .
--   $$
--
--   This is Claim 4 of Jaillet and Lu in the large-$n$ limit; with the reduction of p. 15 it gives the per-advertiser bound behind Theorem 3's ratio $0.706$ for general arrival rates. The minimum of $R$ over this region is about $0.70603$, attained near $(f, \beta, s) = (1, 0.565, \ln 2)$, which is where the paper's grid computation locates it.
--
--   **Formalization Note** The printed Claim 4 assumes $f - s \le (1 - \ln 2) + 1/n$ "for $n \ge 100$". That version is false: at $n = 100$, $(f, \beta, s) = (1,\ 0.55886,\ \ln 2 - 0.01)$ satisfies the hypotheses and gives $R \approx 0.70521 < 0.706$ (planning numerics, confirmed at 30 digits); the printed region satisfies $R \ge 0.706$ only from $n \approx 2929$ on. The statement here takes the limit $n \to \infty$ of the constraint, $f - s \le 1 - \ln 2$, which is the regime in which the paper claims Theorem 3 ("$n$ is large enough so that a factor of $1 + O(1/n)$ is negligible", p. 6); the constant $0.706$ is unchanged. Second, the page allows $\beta = 0$; here $\beta > 0$ is required because $s/\beta$ would be $0$ in Lean, and $R(1, 0, 1) \approx 0.607$. In the paper $\beta_a = 0$ forces $s_a = 0$, and that case is covered by the mission's goal directly. The constraint $f > 0$ follows from $f \ge \beta > 0$.
-- source:
--   Jaillet & Lu, Online Stochastic Matching: New Algorithms with Better Bounds, accepted manuscript (rev. June 2013), p. 16, Claim 4 (stated with the limit constraint f − s ≤ 1 − ln 2; the printed "+ 1/n, n ≥ 100" version is false)

import Mathlib
import Definitions.Def_RandomListsMatching_GeneralRates_Setting

namespace RandomListsMatching.GeneralRates

theorem claim4_R_lower_bound (f β s : ℝ) (hf1 : f ≤ 1) (hsf : s ≤ f) (hβs : β ≤ s)
    (hβ : 0 < β) (hgap : f - s ≤ 1 - Real.log 2) :
    (0.706 : ℝ) ≤ R f β s := by sorry

end RandomListsMatching.GeneralRates
