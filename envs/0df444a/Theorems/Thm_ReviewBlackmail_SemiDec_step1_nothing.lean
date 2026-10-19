-- Prove2me | Theorems.Thm_ReviewBlackmail_SemiDec_step1_nothing
-- name    : ReviewBlackmail.SemiDec.step1_nothing
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T02:32:47.049026+00:00
-- url     : https://prove2.me/theorems/764008b3-a0f2-48cf-ac29-5bcab520e01d
-- title:
--   Proof of Proposition 5, Step 1, p. 42 — i = n is an equilibrium iff r ≥ π(a) − π(a^n_N) and b ≥ (1 − γ(1 − δ))/(1 − δ)(π(a) − π(a^n_N))
-- statement:
--   In the semi-decentralized game with genuine reviews kept, under the standing assumptions and $\delta<1$, doing nothing ($i=n$) is an equilibrium response to a ransom demand $r$ if and only if
--   $$r\ge\pi(a)-\pi(a^n_N)\qquad\text{and}\qquad b\ge\frac{1-\gamma(1-\delta)}{1-\delta}\big(\pi(a)-\pi(a^n_N)\big).$$
--
--   The second inequality is the penalty threshold separating the two regimes of Proposition 5.
--
--   **Formalization Note** $\delta<1$ is added: the paper divides by $1-\delta$; at $\delta=1$ Lean's convention $x/0=0$ would change the condition.
-- source:
--   Papanastasiou, Yang, Zhang, Improving Dispute Resolution in Two-Sided Platforms: The Case of Review Blackmail, accepted manuscript (LBS Research Online eprint 1988; Management Science 69(10), 2023, doi:10.1287/mnsc.2022.4655), p. 42, Proof of Proposition 5, Step 1

import Mathlib
import Definitions.Def_ReviewBlackmail_SemiDec_Setting

namespace ReviewBlackmail.SemiDec
theorem step1_nothing (M : Model) (hM : M.Standing) (hδ : M.δ < 1) (r : ℝ) :
    M.IsEq .n r ↔
      M.fut M.a - M.fut (M.post 1 1 .N) ≤ r ∧
        (1 - M.γ * (1 - M.δ)) / (1 - M.δ) * (M.fut M.a - M.fut (M.post 1 1 .N)) ≤ M.b := by sorry
end ReviewBlackmail.SemiDec
