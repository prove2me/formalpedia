-- Prove2me | Theorems.Thm_ReviewBlackmail_SemiDec_step1_mechanism
-- name    : ReviewBlackmail.SemiDec.step1_mechanism
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T02:32:54.347548+00:00
-- url     : https://prove2.me/theorems/d3afa79d-d1d2-4057-8bfc-d09b84084e3c
-- title:
--   Proof of Proposition 5, Step 1, p. 42 — i = d is an equilibrium iff b ≤ (1 − γ(1 − δ))/(1 − δ)(π(a) − π(a^d_N)) and r ≥ (1 − δ)(γ(π(a) − π(a^d_N)) + b)
-- statement:
--   In the semi-decentralized game with genuine reviews kept, under the standing assumptions and $\delta<1$, using the mechanism ($i=d$) is an equilibrium response to a ransom demand $r$ — when the market believes the seller uses the mechanism, its payoff $(1-\gamma(1-\delta))\pi(a^d_0)+\gamma(1-\delta)\pi(a^d_N)-(1-\delta)b$ is at least that of doing nothing, $\pi(a^d_N)$, and of settling, $\pi(a^d_0)-r$ — if and only if
--   $$b\le\frac{1-\gamma(1-\delta)}{1-\delta}\big(\pi(a)-\pi(a^d_N)\big)\qquad\text{and}\qquad r\ge(1-\delta)\big(\gamma(\pi(a)-\pi(a^d_N))+b\big).$$
--
--   The second inequality says that the ransom must exceed the seller's expected loss from the mechanism; it is the ransom (7) of Proposition 5.
--
--   **Formalization Note** $\delta<1$ is added (division by $1-\delta$). The page simplifies the second displayed inequality to "$b\le\gamma(\pi(a)-\pi(a^d_N))-r$", which drops the factor $1-\delta$ and the sign of $b$; the correct simplification, stated here, is the one Step 2 of the proof uses.
-- source:
--   Papanastasiou, Yang, Zhang, Improving Dispute Resolution in Two-Sided Platforms: The Case of Review Blackmail, accepted manuscript (LBS Research Online eprint 1988; Management Science 69(10), 2023, doi:10.1287/mnsc.2022.4655), p. 42, Proof of Proposition 5, Step 1

import Mathlib
import Definitions.Def_ReviewBlackmail_SemiDec_Setting

namespace ReviewBlackmail.SemiDec
theorem step1_mechanism (M : Model) (hM : M.Standing) (hδ : M.δ < 1) (r : ℝ) :
    M.IsEq .d r ↔
      M.b ≤ (1 - M.γ * (1 - M.δ)) / (1 - M.δ) *
          (M.fut M.a - M.fut (M.post (M.γ * (1 - M.δ)) 1 .N)) ∧
        (1 - M.δ) * (M.γ * (M.fut M.a - M.fut (M.post (M.γ * (1 - M.δ)) 1 .N)) + M.b) ≤ r := by sorry
end ReviewBlackmail.SemiDec
