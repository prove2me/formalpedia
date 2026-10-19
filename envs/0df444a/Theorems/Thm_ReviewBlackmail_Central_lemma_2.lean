-- Prove2me | Theorems.Thm_ReviewBlackmail_Central_lemma_2
-- name    : ReviewBlackmail.Central.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T02:32:45.946491+00:00
-- url     : https://prove2.me/theorems/a3954dd8-7389-42ba-a85e-d5dddb04ff49
-- title:
--   Lemma 2, p. 11 — the posterior beliefs $a^i_P = 1$, $a^i_0 = a$, $a^i_N \in [0, a]$ and the closed forms of $a^n_N$, $a^c_N$, $a^s_N$
-- statement:
--   Consider the review-blackmail model under centralized dispute resolution with the standing assumptions ($a,\theta,\beta\in(0,1)$, $0<p<a\theta$, $\pi$ nonnegative, convex and strictly increasing on $[0,1]$, $c\ge 0$), and let the timeliness $\gamma$ and accuracy $\delta$ lie in $[0,1]$. Let $a^i_R$ be the market's Bayes posterior that quality is high after observing review $R\in\{N,0,P\}$ when it believes the seller responds to a malicious review with $i\in\{s,n,c\}$.
--
--   Then for every $i$,
--   $$a^i_P=1,\qquad a^i_0=a,\qquad a^i_N\in[0,a],$$
--   and, writing $\rho=1-\frac{p}{a\theta}$,
--   $$a^n_N=\frac{a}{a+(1-a)\dfrac{\beta+(1-\beta)\rho}{\beta+(1-\beta)\rho(1-\theta)}},\qquad a^c_N=\frac{a}{a+(1-a)\dfrac{\beta(1-\gamma\delta)+(1-\beta)\rho}{\beta(1-\gamma\delta)+(1-\beta)\rho(1-\theta)}},$$
--   $$a^s_N=\frac{a}{a+(1-a)\frac{1}{1-\theta}}.$$
--
--   A positive review can only come from a high-quality product, the absence of a review carries no information about quality, and a negative review lowers the belief by an amount that depends on how the market expects the seller to handle blackmail. The closed forms are what Propositions 1–2 and Corollary 1 compare.
--
--   **Formalization Note** $a^i_R$ is `M.post (keep (γ * δ) i) R`, defined by Bayes' rule from the likelihood table, so the closed forms are a computation, not a definition. The closed forms are transcribed as printed, with $1-p/(a\theta)$ written out.
-- source:
--   Papanastasiou, Yang, Zhang, Improving Dispute Resolution in Two-Sided Platforms: The Case of Review Blackmail, accepted manuscript (LBS Research Online eprint 1988; Management Science 69(10), 2023, doi:10.1287/mnsc.2022.4655), p. 11, Lemma 2 (proof pp. 35–36, (15)–(16))

import Mathlib
import Definitions.Def_ReviewBlackmail_Central_Setting

namespace ReviewBlackmail.Central

theorem lemma_2 (M : Model) (hM : M.Standing) (γ δ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1)
    (hδ : δ ∈ Set.Icc (0 : ℝ) 1) :
    (∀ i : Resp, M.post (keep (γ * δ) i) .P = 1 ∧ M.post (keep (γ * δ) i) .Z = M.a ∧
      M.post (keep (γ * δ) i) .N ∈ Set.Icc 0 M.a) ∧
    M.post (keep (γ * δ) .n) .N =
      M.a / (M.a + (1 - M.a) * ((M.β + (1 - M.β) * (1 - M.p / (M.a * M.θ))) /
        (M.β + (1 - M.β) * (1 - M.p / (M.a * M.θ)) * (1 - M.θ)))) ∧
    M.post (keep (γ * δ) .c) .N =
      M.a / (M.a + (1 - M.a) * ((M.β * (1 - γ * δ) + (1 - M.β) * (1 - M.p / (M.a * M.θ))) /
        (M.β * (1 - γ * δ) + (1 - M.β) * (1 - M.p / (M.a * M.θ)) * (1 - M.θ)))) ∧
    M.post (keep (γ * δ) .s) .N = M.a / (M.a + (1 - M.a) * (1 / (1 - M.θ))) := by sorry

end ReviewBlackmail.Central
