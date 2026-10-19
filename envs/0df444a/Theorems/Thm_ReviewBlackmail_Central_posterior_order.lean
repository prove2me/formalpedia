-- Prove2me | Theorems.Thm_ReviewBlackmail_Central_posterior_order
-- name    : ReviewBlackmail.Central.posterior_order
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T02:32:49.918646+00:00
-- url     : https://prove2.me/theorems/c1971bfb-3bd7-4950-8ebb-34a7d5397d6c
-- title:
--   §4.1, p. 11 — $a^s_N < a^c_N < a^n_N$
-- statement:
--   Under the standing assumptions of the centralized review-blackmail model, let $\gamma,\delta\in[0,1]$ with $0<\gamma\delta<1$. Then the posteriors after a negative review are strictly ordered:
--   $$a^s_N<a^c_N<a^n_N.$$
--
--   A negative review is most damaging when the market believes the seller settles every blackmail attempt (then it can only come from a regular consumer) and least damaging when it believes the seller ignores them; the centralized mechanism sits in between. This ordering drives the equilibrium analysis of Propositions 1–2 and the jump of Corollary 1.
--
--   **Formalization Note** The page states the ordering as a consequence of Lemma 2 for the general $\gamma\delta$; the hypothesis $0<\gamma\delta<1$ is added because at $\gamma\delta=0$ one has $a^c_N=a^n_N$ and at $\gamma\delta=1$ one has $a^c_N=a^s_N$, so strictness fails there.
-- source:
--   Papanastasiou, Yang, Zhang, Improving Dispute Resolution in Two-Sided Platforms: The Case of Review Blackmail, accepted manuscript (LBS Research Online eprint 1988; Management Science 69(10), 2023, doi:10.1287/mnsc.2022.4655), §4.1, p. 11, after Lemma 2

import Mathlib
import Definitions.Def_ReviewBlackmail_Central_Setting

namespace ReviewBlackmail.Central

theorem posterior_order (M : Model) (hM : M.Standing) (γ δ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1)
    (hδ : δ ∈ Set.Icc (0 : ℝ) 1) (hpos : 0 < γ * δ) (hlt : γ * δ < 1) :
    M.post (keep (γ * δ) .s) .N < M.post (keep (γ * δ) .c) .N ∧
      M.post (keep (γ * δ) .c) .N < M.post (keep (γ * δ) .n) .N := by sorry

end ReviewBlackmail.Central
