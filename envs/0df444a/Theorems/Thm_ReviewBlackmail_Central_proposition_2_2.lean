-- Prove2me | Theorems.Thm_ReviewBlackmail_Central_proposition_2_2
-- name    : ReviewBlackmail.Central.proposition_2_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T02:32:47.999544+00:00
-- url     : https://prove2.me/theorems/0d8a173d-f560-4cb8-8118-b1bfce74163a
-- title:
--   Proposition 2(2), p. 13 — when $c < \gamma\delta(\pi(a) - \pi(a^n_N))$, $r^* = (1 - \gamma\delta)[\pi(a) - \pi(a^c_N)] + c$ and the malicious consumer purchases iff $p < r^*$
-- statement:
--   Under the standing assumptions of the centralized review-blackmail model, let $\gamma,\delta\in[0,1]$ and suppose the mechanism efficiency is high relative to its cost,
--   $$c\ <\ \gamma\delta\,\big(\pi(a)-\pi(a^n_N)\big).$$
--   Then:
--   1. the greatest ransom at which settling is the prevailing (seller-preferred) equilibrium is
--   $$r^*=(1-\gamma\delta)\big[\pi(a)-\pi(a^c_N)\big]+c;$$
--   2. the malicious consumer purchases if and only if $p<(1-\gamma\delta)[\pi(a)-\pi(a^c_N)]+c$.
--
--   In this regime the mechanism caps the ransom: a higher demand would make reporting the seller's preferred response.
--
--   **Formalization Note** $r^*$ is the greatest element (`IsGreatest`) of the set of ransoms at which settling prevails; the set is not restricted to $r>0$ (at $\gamma\delta=1$ and $c=0$ the ransom is $0$). No hypothesis beyond the standing assumptions and $\gamma,\delta\in[0,1]$ is added.
-- source:
--   Papanastasiou, Yang, Zhang, Improving Dispute Resolution in Two-Sided Platforms: The Case of Review Blackmail, accepted manuscript (LBS Research Online eprint 1988; Management Science 69(10), 2023, doi:10.1287/mnsc.2022.4655), p. 13, Proposition 2(2), (2)

import Mathlib
import Definitions.Def_ReviewBlackmail_Central_Setting

namespace ReviewBlackmail.Central

theorem proposition_2_2 (M : Model) (hM : M.Standing) (γ δ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1)
    (hδ : δ ∈ Set.Icc (0 : ℝ) 1)
    (hcase : M.c < γ * δ * (M.π M.a - M.π (M.post (keep (γ * δ) .n) .N))) :
    IsGreatest {r : ℝ | M.SettlePrevails (γ * δ) r}
        ((1 - γ * δ) * (M.π M.a - M.π (M.post (keep (γ * δ) .c) .N)) + M.c) ∧
      (M.Purchases (γ * δ) ↔
        M.p < (1 - γ * δ) * (M.π M.a - M.π (M.post (keep (γ * δ) .c) .N)) + M.c) := by sorry

end ReviewBlackmail.Central
