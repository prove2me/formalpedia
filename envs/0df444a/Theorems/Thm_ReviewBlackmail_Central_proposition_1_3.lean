-- Prove2me | Theorems.Thm_ReviewBlackmail_Central_proposition_1_3
-- name    : ReviewBlackmail.Central.proposition_1_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:32:51.869472+00:00
-- url     : https://prove2.me/theorems/fb54dc0f-a935-471c-bedf-1096408636bb
-- title:
--   Proposition 1(3), p. 13 — an equilibrium with $i = c$ (report) exists iff $\pi(a) + (c - r)/(1 - \gamma\delta) \le \pi(a^c_N) \le \pi(a) - c/\gamma\delta$
-- statement:
--   Suppose a malicious consumer enters the system, posts a negative review, and demands a ransom $r$. Under the standing assumptions of the centralized review-blackmail model, with $\gamma,\delta\in[0,1]$ and $0<\gamma\delta<1$, reporting the review to the centralized mechanism ($i=c$) is an equilibrium response if and only if
--   $$\pi(a)+\frac{c-r}{1-\gamma\delta}\ \le\ \pi(a^c_N)\ \le\ \pi(a)-\frac{c}{\gamma\delta}.$$
--
--   Using the mechanism is an equilibrium when its efficiency is high and the ransom is not too low.
--
--   **Formalization Note** The statement holds for every real $r$. The hypothesis $0<\gamma\delta<1$ is added because the page divides by $\gamma\delta$ and by $1-\gamma\delta$.
-- source:
--   Papanastasiou, Yang, Zhang, Improving Dispute Resolution in Two-Sided Platforms: The Case of Review Blackmail, accepted manuscript (LBS Research Online eprint 1988; Management Science 69(10), 2023, doi:10.1287/mnsc.2022.4655), pp. 12–13, Proposition 1(3)

import Mathlib
import Definitions.Def_ReviewBlackmail_Central_Setting

namespace ReviewBlackmail.Central

theorem proposition_1_3 (M : Model) (hM : M.Standing) (γ δ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1)
    (hδ : δ ∈ Set.Icc (0 : ℝ) 1) (hpos : 0 < γ * δ) (hlt : γ * δ < 1) (r : ℝ) :
    M.IsEq (γ * δ) .c r ↔
      M.π M.a + (M.c - r) / (1 - γ * δ) ≤ M.π (M.post (keep (γ * δ) .c) .N) ∧
        M.π (M.post (keep (γ * δ) .c) .N) ≤ M.π M.a - M.c / (γ * δ) := by sorry

end ReviewBlackmail.Central
