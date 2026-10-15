-- Prove2me | Theorems.Thm_ReviewBlackmail_SemiDec_posterior_order
-- name    : ReviewBlackmail.SemiDec.posterior_order
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:32:50.925761+00:00
-- url     : https://prove2.me/theorems/de0ef807-db47-4283-b2a4-f163648c4d11
-- title:
--   §5.1, p. 21 — a^s_N < a^d_N < a^n_N
-- statement:
--   Under the standing assumptions of the semi-decentralized model, suppose that the probability $\gamma(1-\delta)$ with which a malicious review removed through the mechanism is reinstated satisfies $0<\gamma(1-\delta)<1$. Then the posteriors after a negative review are strictly ordered:
--   $$a^s_N<a^d_N<a^n_N.$$
--
--   A negative review is least informative of low quality when the seller is believed to ignore blackmail (it may be the blackmailer's), most informative when he is believed to settle (it must be genuine), and in between under the mechanism. The ordering is what makes the ransom thresholds of Proposition 5 comparable.
--
--   **Formalization Note** The bounds $0<\gamma(1-\delta)<1$ are added: at $\gamma(1-\delta)=0$ one has $a^d_N=a^s_N$ and at $\gamma(1-\delta)=1$ one has $a^d_N=a^n_N$, so the strict ordering the paper states needs both.
-- source:
--   Papanastasiou, Yang, Zhang, Improving Dispute Resolution in Two-Sided Platforms: The Case of Review Blackmail, accepted manuscript (LBS Research Online eprint 1988; Management Science 69(10), 2023, doi:10.1287/mnsc.2022.4655), p. 21, §5.1, after (5)

import Mathlib
import Definitions.Def_ReviewBlackmail_SemiDec_Setting

namespace ReviewBlackmail.SemiDec
theorem posterior_order (M : Model) (hM : M.Standing)
    (h0 : 0 < M.γ * (1 - M.δ)) (h1 : M.γ * (1 - M.δ) < 1) :
    M.post 0 1 .N < M.post (M.γ * (1 - M.δ)) 1 .N ∧
      M.post (M.γ * (1 - M.δ)) 1 .N < M.post 1 1 .N := by sorry
end ReviewBlackmail.SemiDec
