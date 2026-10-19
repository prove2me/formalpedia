-- Prove2me | Theorems.Thm_ReviewBlackmail_Central_proposition_1_1
-- name    : ReviewBlackmail.Central.proposition_1_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T02:32:52.921483+00:00
-- url     : https://prove2.me/theorems/0664ffa2-a09c-4590-a41b-fe635d0f8012
-- title:
--   Proposition 1(1), p. 13 — an equilibrium with $i = n$ (ignore the blackmail) exists iff $\pi(a^n_N) \ge \max\{\pi(a) - r, \pi(a) - c/\gamma\delta\}$
-- statement:
--   Suppose a malicious consumer enters the system, posts a negative review, and demands a ransom $r$. Under the standing assumptions of the centralized review-blackmail model, with $\gamma,\delta\in[0,1]$ and $0<\gamma\delta<1$, doing nothing ($i=n$) is an equilibrium response, i.e. the seller has no profitable deviation when the market believes he ignores blackmail, if and only if
--   $$\pi(a^n_N)\ \ge\ \max\Big\{\pi(a)-r,\ \pi(a)-\frac{c}{\gamma\delta}\Big\}.$$
--
--   Ignoring the blackmail is an equilibrium when the ransom is high and the mechanism is inefficient.
--
--   **Formalization Note** The statement holds for every real $r$. The hypothesis $0<\gamma\delta<1$ is added because the page divides by $\gamma\delta$ (at $\gamma\delta=0$ the page means $c/0=+\infty$, while Lean's $c/0=0$ would make the statement false).
-- source:
--   Papanastasiou, Yang, Zhang, Improving Dispute Resolution in Two-Sided Platforms: The Case of Review Blackmail, accepted manuscript (LBS Research Online eprint 1988; Management Science 69(10), 2023, doi:10.1287/mnsc.2022.4655), pp. 12–13, Proposition 1(1)

import Mathlib
import Definitions.Def_ReviewBlackmail_Central_Setting

namespace ReviewBlackmail.Central

theorem proposition_1_1 (M : Model) (hM : M.Standing) (γ δ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1)
    (hδ : δ ∈ Set.Icc (0 : ℝ) 1) (hpos : 0 < γ * δ) (hlt : γ * δ < 1) (r : ℝ) :
    M.IsEq (γ * δ) .n r ↔
      max (M.π M.a - r) (M.π M.a - M.c / (γ * δ)) ≤ M.π (M.post (keep (γ * δ) .n) .N) := by sorry

end ReviewBlackmail.Central
