-- Prove2me | Theorems.Thm_SCInfoDesign_Intersecting_gammaStarIS_posteriors
-- name    : SCInfoDesign.Intersecting.gammaStarIS_posteriors
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:18:56.738012+00:00
-- url     : https://prove2.me/theorems/117736a5-4a96-4fc5-b358-36ae12a0c69f
-- title:
--   App. C.1, p. 32 — under Γ*_IS, ℙ(m₀) = p₀/p̆ with posterior p̆, and m₁ induces posterior 0
-- statement:
--   Assume $b_0>b_1>a_0>a_1\ge 0$ and $0<\xi<1$, and let $p_0\ge 0$ satisfy $\xi<\underline\tau_{\mathsf{IS}}(p_0)$ (so $p_0<1$). Then the partial-disclosure map $\pi^*_{\mathsf{IS}}$ of (7) is a policy, and with $\breve p=1-\xi(b_1-a_1)/(a_0-a_1)$,
--   $$
--   \mathbb P(m_0)=\pi^*_{\mathsf{IS}}(m_0\mid\omega=0)p_0+\pi^*_{\mathsf{IS}}(m_0\mid\omega=1)(1-p_0)=\frac{p_0}{\breve p},\qquad \mathbb P(m_1)=1-\frac{p_0}{\breve p}.
--   $$
--   If $p_0>0$, the supplier's posterior after $m_0$ is $\breve p$; after $m_1$ it is $0$.
--
--   So $\Gamma^*_{\mathsf{IS}}$ splits the prior $p_0$ into the posteriors $0$ and $\breve p$, which is how it attains the chord value of Lemma 2.
--
--   **Formalization Note** The paper's sentence says the posterior becomes $0$ "after message $m_1$ whose probability is $\mathbb P(m_0)=\cdots$"; as (7) and $\mathbb P(m_1)=1-p_0/\breve p$ show, $m_0$ (probability $p_0/\breve p$) induces $\breve p$ and $m_1$ induces $0$, which is what is stated. At $p_0=0$ message $m_0$ has probability $0$ and its posterior is a junk value, so that conjunct assumes $p_0>0$.
-- source:
--   Candogan, Gurkan, The Value of Information Design in Supply Chain Management, SSRN 4378997 (preprint), p. 32, proof of Proposition 3, display for ℙ(m₀) and the sentences around it; (7) p. 15

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_convexEnvelope
import Definitions.Def_SCInfoDesign_Intersecting_Setting

namespace SCInfoDesign.Intersecting
theorem gammaStarIS_posteriors (P : Params) (ha₁0 : 0 ≤ P.a₁) (hξ0 : 0 < P.ξ) (hξ1 : P.ξ < 1)
    (hb : P.b₁ < P.b₀) (hm : P.a₀ < P.b₁) (ha : P.a₁ < P.a₀)
    (p₀ : ℝ) (hp₀ : 0 ≤ p₀) (hreg : P.ξ < P.τlowIS p₀) :
    SCInfoDesign.Nested.IsPolicy (P.gammaStarIS p₀) ∧
    SCInfoDesign.Nested.msgProb p₀ (P.gammaStarIS p₀) 0 = p₀ / P.pbreve ∧
    SCInfoDesign.Nested.msgProb p₀ (P.gammaStarIS p₀) 1 = 1 - p₀ / P.pbreve ∧
    (0 < p₀ → SCInfoDesign.Nested.posterior p₀ (P.gammaStarIS p₀) 0 = P.pbreve) ∧
    SCInfoDesign.Nested.posterior p₀ (P.gammaStarIS p₀) 1 = 0 := by sorry
end SCInfoDesign.Intersecting
