-- Prove2me | Theorems.Thm_ReviewBlackmail_SemiDec_eq5_posteriors
-- name    : ReviewBlackmail.SemiDec.eq5_posteriors
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T02:32:50.103164+00:00
-- url     : https://prove2.me/theorems/4678dd89-aa87-4362-8ba6-08bc07d7bc85
-- title:
--   (5), p. 21 — the posterior a^d_N after a negative review under the semi-decentralized mechanism, and a^i_0 = a
-- statement:
--   Under the standing assumptions of the semi-decentralized model, the posterior beliefs produced by Bayes' rule have the following closed forms. Write $\rho=1-p/(a\theta)$ and let $a_R(m,1)$ be the market's posterior after review $R$ when a malicious negative review stays visible with probability $m$ and genuine reviews are kept.
--
--   1. No review leaves the belief at the prior: $a_0(m,1)=a$ for every $m\in[0,1]$; in particular $a^s_0=a^n_0=a^d_0=a$.
--   2. Under the mechanism ($m=\gamma(1-\delta)$), the posterior after a negative review is (5):
--   $$a^d_N=\frac{a}{a+(1-a)\dfrac{\beta\gamma(1-\delta)+(1-\beta)\left(1-\frac{p}{a\theta}\right)}{\beta\gamma(1-\delta)+(1-\beta)\left(1-\frac{p}{a\theta}\right)(1-\theta)}}.$$
--   3. Doing nothing ($m=1$) and settling ($m=0$) give Lemma 2's
--   $$a^n_N=\frac{a}{a+(1-a)\dfrac{\beta+(1-\beta)\left(1-\frac{p}{a\theta}\right)}{\beta+(1-\beta)\left(1-\frac{p}{a\theta}\right)(1-\theta)}},\qquad a^s_N=\frac{a}{a+(1-a)\frac{1}{1-\theta}}.$$
--
--   These are the beliefs in terms of which Proposition 5's thresholds and ransoms are written.
--
--   **Formalization Note** The posteriors are `post m 1 R` of the setting, defined by Bayes' rule over the likelihood table; this theorem links them to the printed closed forms. The paper states $a^d_0=a$ in Step 2 of the proof of Proposition 5 (p. 42); the general form for all $m\in[0,1]$ is Lemma 2's $a^i_0=a$ extended to the mechanism.
-- source:
--   Papanastasiou, Yang, Zhang, Improving Dispute Resolution in Two-Sided Platforms: The Case of Review Blackmail, accepted manuscript (LBS Research Online eprint 1988; Management Science 69(10), 2023, doi:10.1287/mnsc.2022.4655), p. 21, §5.1, (5); p. 11, Lemma 2; p. 42, Proof of Proposition 5, Step 2, (22)

import Mathlib
import Definitions.Def_ReviewBlackmail_SemiDec_Setting

namespace ReviewBlackmail.SemiDec
theorem eq5_posteriors (M : Model) (hM : M.Standing) :
    (∀ m ∈ Set.Icc (0 : ℝ) 1, M.post m 1 .Z = M.a) ∧
    M.post (M.γ * (1 - M.δ)) 1 .N =
      M.a / (M.a + (1 - M.a) *
        ((M.β * M.γ * (1 - M.δ) + (1 - M.β) * (1 - M.p / (M.a * M.θ))) /
          (M.β * M.γ * (1 - M.δ) + (1 - M.β) * (1 - M.p / (M.a * M.θ)) * (1 - M.θ)))) ∧
    M.post 1 1 .N =
      M.a / (M.a + (1 - M.a) *
        ((M.β + (1 - M.β) * (1 - M.p / (M.a * M.θ))) /
          (M.β + (1 - M.β) * (1 - M.p / (M.a * M.θ)) * (1 - M.θ)))) ∧
    M.post 0 1 .N = M.a / (M.a + (1 - M.a) * (1 / (1 - M.θ))) := by sorry
end ReviewBlackmail.SemiDec
