-- Prove2me | Theorems.Thm_ReviewBlackmail_Central_corollary_1
-- name    : ReviewBlackmail.Central.corollary_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:32:53.433399+00:00
-- url     : https://prove2.me/theorems/2c7963b1-9cd4-4777-85b6-d91e2fbbef4c
-- title:
--   Corollary 1, p. 14 — the equilibrium ransom $r^*$ is not monotonically decreasing in the mechanism efficiency $\gamma\delta$
-- statement:
--   Under the standing assumptions of the centralized review-blackmail model, suppose the hassle cost is positive, $c>0$, and
--   $$p\ <\ \pi(a)-\pi(a^n_N)-c,$$
--   which is the corollary's hypothesis $p<(1-\gamma\delta)[\pi(a)-\pi(a^n_N)]$ read at the efficiency $\gamma\delta=c/(\pi(a)-\pi(a^n_N))$ where the two regimes of Proposition 2 meet. Then the equilibrium ransom is not monotonically decreasing in the mechanism efficiency $e=\gamma\delta$: there are efficiencies
--   $$0\le e_1<e_2\le 1$$
--   such that the malicious consumer purchases at both, $p<(1-e_k)[\pi(a)-\pi(a^n_N)]$ for $k=1,2$, the equilibrium ransoms $r^*(e_1)$ and $r^*(e_2)$ (the greatest ransoms at which settling prevails) exist, and
--   $$r^*(e_1)<r^*(e_2).$$
--
--   So making the platform's mechanism more efficient can increase the ransom a blackmailer extracts: $r^*$ jumps upward where the regime of Proposition 2(1) gives way to that of Proposition 2(2).
--
--   **Formalization Note** "Not monotonically decreasing" is read as "not nonincreasing", i.e. the existence of $e_1<e_2$ with $r^*(e_1)<r^*(e_2)$; the reading "not strictly decreasing" would hold trivially if $r^*$ were constant. The efficiency $e=\gamma\delta$ is quantified directly over $[0,1]$ (every $e\in[0,1]$ is $\gamma\delta$ with $\gamma=e$, $\delta=1$). The posterior $a^n_N$ does not depend on the efficiency and is written `M.post 1 .N` (visibility probability $1$ of a malicious review). The hypothesis $c>0$ is a disclosed addition: the model allows $c\ge 0$, but at $c=0$ the corollary is false, since then $r^*(e)=(1-e)[\pi(a)-\pi(a^c_N)]$ is nonincreasing in $e$.
-- source:
--   Papanastasiou, Yang, Zhang, Improving Dispute Resolution in Two-Sided Platforms: The Case of Review Blackmail, accepted manuscript (LBS Research Online eprint 1988; Management Science 69(10), 2023, doi:10.1287/mnsc.2022.4655), p. 14, Corollary 1 (proof pp. 39–40)

import Mathlib
import Definitions.Def_ReviewBlackmail_Central_Setting

namespace ReviewBlackmail.Central

theorem corollary_1 (M : Model) (hM : M.Standing) (hc : 0 < M.c)
    (hp : M.p < M.π M.a - M.π (M.post 1 .N) - M.c) :
    ∃ e₁ e₂ r₁ r₂ : ℝ, 0 ≤ e₁ ∧ e₁ < e₂ ∧ e₂ ≤ 1 ∧
      M.p < (1 - e₁) * (M.π M.a - M.π (M.post 1 .N)) ∧
      M.p < (1 - e₂) * (M.π M.a - M.π (M.post 1 .N)) ∧
      IsGreatest {r : ℝ | M.SettlePrevails e₁ r} r₁ ∧
      IsGreatest {r : ℝ | M.SettlePrevails e₂ r} r₂ ∧
      r₁ < r₂ := by sorry

end ReviewBlackmail.Central
