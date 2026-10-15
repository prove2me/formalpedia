-- Prove2me | Theorems.Thm_ReviewBlackmail_Central_proposition_2_1
-- name    : ReviewBlackmail.Central.proposition_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:32:47.83908+00:00
-- url     : https://prove2.me/theorems/879dfd47-4646-42e1-b3be-cd2cd472973a
-- title:
--   Proposition 2(1), p. 13 — when $c \ge \gamma\delta(\pi(a) - \pi(a^n_N))$, $r^* = \pi(a) - \pi(a^n_N)$ and the malicious consumer purchases iff $p < r^*$
-- statement:
--   Under the standing assumptions of the centralized review-blackmail model, let $\gamma,\delta\in[0,1]$ and suppose the mechanism efficiency is low relative to its cost,
--   $$c\ \ge\ \gamma\delta\,\big(\pi(a)-\pi(a^n_N)\big).$$
--   Then:
--   1. the greatest ransom at which settling is the prevailing (seller-preferred) equilibrium is
--   $$r^*=\pi(a)-\pi(a^n_N);$$
--   2. the malicious consumer purchases (i.e. some ransom at which settling prevails exceeds $p$) if and only if $p<\pi(a)-\pi(a^n_N)$.
--
--   In this regime the mechanism has no effect on the blackmail: the consumer extracts exactly the seller's loss from a visible negative review under the belief that he ignores blackmail.
--
--   **Formalization Note** "Demands a ransom $r^*$" is formalized as: $r^*$ is the greatest element (`IsGreatest`) of the set of ransoms $r$ at which settling prevails, as in the proof ("the maximum possible ransom such that $i=s$ is the seller's preferred equilibrium", p. 38). No hypothesis beyond the standing assumptions and $\gamma,\delta\in[0,1]$ is added; the statement involves no division.
-- source:
--   Papanastasiou, Yang, Zhang, Improving Dispute Resolution in Two-Sided Platforms: The Case of Review Blackmail, accepted manuscript (LBS Research Online eprint 1988; Management Science 69(10), 2023, doi:10.1287/mnsc.2022.4655), p. 13, Proposition 2(1), (1)

import Mathlib
import Definitions.Def_ReviewBlackmail_Central_Setting

namespace ReviewBlackmail.Central

theorem proposition_2_1 (M : Model) (hM : M.Standing) (γ δ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1)
    (hδ : δ ∈ Set.Icc (0 : ℝ) 1)
    (hcase : γ * δ * (M.π M.a - M.π (M.post (keep (γ * δ) .n) .N)) ≤ M.c) :
    IsGreatest {r : ℝ | M.SettlePrevails (γ * δ) r}
        (M.π M.a - M.π (M.post (keep (γ * δ) .n) .N)) ∧
      (M.Purchases (γ * δ) ↔ M.p < M.π M.a - M.π (M.post (keep (γ * δ) .n) .N)) := by sorry

end ReviewBlackmail.Central
