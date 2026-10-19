-- Prove2me | Theorems.Thm_ReviewBlackmail_Central_proposition_1_2
-- name    : ReviewBlackmail.Central.proposition_1_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T02:32:52.419471+00:00
-- url     : https://prove2.me/theorems/883ed5e1-9be9-4291-b12b-06a8a42db7e8
-- title:
--   Proposition 1(2), p. 13 — an equilibrium with $i = s$ (settle) exists iff $\pi(a^s_N) \le \min\{\pi(a) - r, \pi(a) + (c - r)/(1 - \gamma\delta)\}$
-- statement:
--   Suppose a malicious consumer enters the system, posts a negative review, and demands a ransom $r$. Under the standing assumptions of the centralized review-blackmail model, with $\gamma,\delta\in[0,1]$ and $0<\gamma\delta<1$, settling ($i=s$) is an equilibrium response if and only if
--   $$\pi(a^s_N)\ \le\ \min\Big\{\pi(a)-r,\ \pi(a)+\frac{c-r}{1-\gamma\delta}\Big\}.$$
--
--   Settling is an equilibrium when the ransom demand is small enough.
--
--   **Formalization Note** The statement holds for every real $r$. The hypothesis $0<\gamma\delta<1$ is added because the page divides by $1-\gamma\delta$. The last line of the printed proof (p. 37) has $\pi(a)-c/\gamma\delta$ in place of the second term; that is a typo, and the statement is formalized as printed in the proposition.
-- source:
--   Papanastasiou, Yang, Zhang, Improving Dispute Resolution in Two-Sided Platforms: The Case of Review Blackmail, accepted manuscript (LBS Research Online eprint 1988; Management Science 69(10), 2023, doi:10.1287/mnsc.2022.4655), pp. 12–13, Proposition 1(2)

import Mathlib
import Definitions.Def_ReviewBlackmail_Central_Setting

namespace ReviewBlackmail.Central

theorem proposition_1_2 (M : Model) (hM : M.Standing) (γ δ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1)
    (hδ : δ ∈ Set.Icc (0 : ℝ) 1) (hpos : 0 < γ * δ) (hlt : γ * δ < 1) (r : ℝ) :
    M.IsEq (γ * δ) .s r ↔
      M.π (M.post (keep (γ * δ) .s) .N) ≤
        min (M.π M.a - r) (M.π M.a + (M.c - r) / (1 - γ * δ)) := by sorry

end ReviewBlackmail.Central
