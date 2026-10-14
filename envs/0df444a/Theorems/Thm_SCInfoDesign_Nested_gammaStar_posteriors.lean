-- Prove2me | Theorems.Thm_SCInfoDesign_Nested_gammaStar_posteriors
-- name    : SCInfoDesign.Nested.gammaStar_posteriors
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:30:25.603549+00:00
-- url     : https://prove2.me/theorems/859b8ec5-cdb3-4617-a82c-e809c9a40a5d
-- title:
--   Proof of Theorem 1, App. B, p. 26 — under Γ*, m₀ has probability (p₀ − p̂)/(1 − p̂) and induces posterior 1, m₁ induces p̂
-- statement:
--   In the nested-support model ($0\le a_0\le a_1<b_1\le b_0$, $a_0<b_0$, $0<\xi<1$) let $p_0\in[0,1]$ and suppose
--   $$\xi<\underline\tau(p_0)=\frac{p_0(a_1-a_0)}{b_0-a_0}.$$
--   Let $\hat p=\xi(b_0-a_0)/(a_1-a_0)$ and let $\Gamma^*$ be the two-message policy of (5). Then
--
--   1. $\Gamma^*$ is a policy (its entries are nonnegative and each row sums to $1$);
--   2. message $m_0$ has probability $\mathbb P(m_0)=\dfrac{p_0-\hat p}{1-\hat p}$;
--   3. the posterior after $m_0$ is $1$;
--   4. if $p_0<1$, the posterior after $m_1$ is $\hat p$.
--
--   So $\Gamma^*$ splits the prior $p_0$ into the posteriors $1$ and $\hat p$ with the weights that attain the line segment of the convex envelope in Lemma 1; this is the step that proves the third bullet of Theorem 1.
--
--   **Formalization Note** The strict inequality $\xi<\underline\tau(p_0)$ (rather than the theorem's $\le$) is what the display needs: it gives $0<\hat p<p_0\le 1$, so no division by $0$ occurs. The posterior after $m_1$ is claimed only for $p_0<1$: at $p_0=1$ the paper's own display gives $\mathbb P(m_1)=1-(p_0-\hat p)/(1-\hat p)=0$, so Bayes' rule leaves that posterior undefined (in Lean it is the junk value $0\ne\hat p$). At $\xi=\underline\tau(p_0)$ the paper notes that $\Gamma^*$ is no disclosure ($\pi^*(m_1\mid\omega=0)=1$); then $m_0$ has probability $0$ and its posterior is not defined. In Lean the messages are $m_0=0$, $m_1=1$.
-- source:
--   Candogan, Gurkan, The Value of Information Design in Supply Chain Management, SSRN 4378997 (preprint), App. B, p. 26, proof of Theorem 1, displays for ℙ(m₀) and ℙ(ω = 0 | m₁)

import Mathlib
import Definitions.Def_SCInfoDesign_Nested_Setting

namespace SCInfoDesign.Nested
theorem gammaStar_posteriors (P : Params)
    (ha : P.a₀ < P.b₀) (ha₁ : P.a₁ < P.b₁) (ha₀0 : 0 ≤ P.a₀) (ha₁0 : 0 ≤ P.a₁)
    (hξ0 : 0 < P.ξ) (hξ1 : P.ξ < 1)
    (hnest_a : P.a₀ ≤ P.a₁) (hnest_b : P.b₁ ≤ P.b₀)
    (p₀ : ℝ) (hp₀ : p₀ ∈ Set.Icc (0:ℝ) 1) (hξτ : P.ξ < P.τlow p₀) :
    IsPolicy (P.gammaStar p₀) ∧
    msgProb p₀ (P.gammaStar p₀) 0 = (p₀ - P.pHat) / (1 - P.pHat) ∧
    posterior p₀ (P.gammaStar p₀) 0 = 1 ∧
    (p₀ < 1 → posterior p₀ (P.gammaStar p₀) 1 = P.pHat) := by sorry
end SCInfoDesign.Nested
