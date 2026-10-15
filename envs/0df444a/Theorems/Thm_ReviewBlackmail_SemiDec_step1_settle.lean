-- Prove2me | Theorems.Thm_ReviewBlackmail_SemiDec_step1_settle
-- name    : ReviewBlackmail.SemiDec.step1_settle
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:32:54.458049+00:00
-- url     : https://prove2.me/theorems/ece469fb-534a-48c3-9eb7-7ee6d7ae19c9
-- title:
--   Proof of Proposition 5, Step 1, pp. 41–42 — i = s is an equilibrium iff r ≤ min(π(a) − π(a^s_N), (1 − δ)(γ(π(a) − π(a^s_N)) + b))
-- statement:
--   In the semi-decentralized game with genuine reviews kept, under the standing assumptions, settling ($i=s$) is an equilibrium response to a ransom demand $r$ — no deviation to doing nothing or to the mechanism is profitable when the market believes the seller settles — if and only if
--   $$r\le\min\Big(\pi(a)-\pi(a^s_N),\ (1-\delta)\big(\gamma(\pi(a)-\pi(a^s_N))+b\big)\Big).$$
--
--   This is the first of the three equilibrium conditions from which the equilibrium ransom of Proposition 5 is derived.
-- source:
--   Papanastasiou, Yang, Zhang, Improving Dispute Resolution in Two-Sided Platforms: The Case of Review Blackmail, accepted manuscript (LBS Research Online eprint 1988; Management Science 69(10), 2023, doi:10.1287/mnsc.2022.4655), pp. 41–42, Proof of Proposition 5, Step 1

import Mathlib
import Definitions.Def_ReviewBlackmail_SemiDec_Setting

namespace ReviewBlackmail.SemiDec
theorem step1_settle (M : Model) (hM : M.Standing) (r : ℝ) :
    M.IsEq .s r ↔
      r ≤ min (M.fut M.a - M.fut (M.post 0 1 .N))
        ((1 - M.δ) * (M.γ * (M.fut M.a - M.fut (M.post 0 1 .N)) + M.b)) := by sorry
end ReviewBlackmail.SemiDec
