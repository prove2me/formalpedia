-- Prove2me | Theorems.Thm_ThirdPartyPricing_General_varphi_increasing
-- name    : ThirdPartyPricing.General.varphi_increasing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:21:12.416375+00:00
-- url     : https://prove2.me/theorems/4d4b8ae9-bbe2-4a3f-b62e-a0e175598c6f
-- title:
--   Proof of Theorem 1, pp. 18–19 — the non-adopter's best response ϕ(p̃) to the algorithm φ̃(·, p̃) is increasing
-- statement:
--   Work in the model of §3 under the standing assumptions, with demand-state support $[\underline a,\bar a]\subseteq[a_0,a_1]$, $\underline a<\bar a$, and continuous density $F'$ on it. Fix $\beta\in[0,1)$ and let $\tilde\phi(a,\tilde p)$ be the algorithm's best response (18) for $\tilde p\in[c,p^{\max}]$ and $a\in[a_0,a_1]$. Let $\varphi(\tilde p)\in[c,p^{\max}]$ be a best response of the non-adopting firm to the algorithm $\tilde\phi(\cdot,\tilde p)$, (19):
--   $$\varphi(\tilde p)\in\arg\max_{p_2\in[c,p^{\max}]}\int_{\underline a}^{\bar a}\pi_2\big(\tilde\phi(a,\tilde p),p_2,a\big)F'(a)\,da.$$
--   Then $\varphi$ is strictly increasing on $[c,p^{\max}]$.
--
--   Equilibrium non-adopter prices are exactly the fixed points of $\varphi$, so this is the monotonicity on which the Tarski argument for Theorem 1 rests.
--
--   **Formalization Note** $\tilde\phi$ and $\varphi$ are arbitrary selections with the argmax properties. As in the previous step, $\beta<1$ is needed for strictness: at $\beta=1$ the algorithm does not depend on $\tilde p$ and $\varphi$ is constant.
-- source:
--   Harrington, Third Party Pricing Algorithms and the Intensity of Competition, working paper (3 November 2020), pp. 18–19, proof of Theorem 1, (19)

import Mathlib
import Definitions.Def_ThirdPartyPricing_General_Model

namespace ThirdPartyPricing.General
open Primitives
theorem varphi_increasing (P : Primitives) (hP : P.Standing) (alo ahi : ℝ) (hA : P.IsSupport alo ahi) (f : ℝ → ℝ) (hf : IsDensity alo ahi f) (β : ℝ) (hβ : β ∈ Set.Ico (0:ℝ) 1) (phiT : ℝ → ℝ → ℝ) (hphiT : ∀ pt ∈ P.prices, ∀ a ∈ P.states, phiT pt a ∈ P.prices ∧ IsMaxOn (P.tpObj β pt a) P.prices (phiT pt a)) (varphi : ℝ → ℝ) (hvarphi : ∀ pt ∈ P.prices, varphi pt ∈ P.prices ∧ IsMaxOn (P.naProfit alo ahi f (phiT pt)) P.prices (varphi pt)) : StrictMonoOn varphi P.prices := by sorry
end ThirdPartyPricing.General
