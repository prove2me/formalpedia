-- Prove2me | Theorems.Thm_TradeCredit_Terms_lemmaC8_concave_thetab
-- name    : TradeCredit.Terms.lemmaC8_concave_thetab
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:09:34.698536+00:00
-- url     : https://prove2.me/theorems/d7899940-da28-4d09-8195-fd9fa3995e15
-- title:
--   Lemma C.8, p. 42 — for every θ_t, Π_s is concave in θ_b when α_b = 0
-- statement:
--   Let the demand density $f$ satisfy the standing assumptions of §3, and let $0<c<1$, $\alpha_t\in[0,1]$, $K>0$ and $\alpha_b=0$. For every $\theta_t$, the supplier's profit (8)
--   $$\theta_b\ \mapsto\ \Pi_s(\theta_b,\theta_t)=K+\int_0^{\theta_t}\bar F(x)\,dx-c\,Q(\theta_b,\theta_t)-\alpha_t\int_{\theta_b}^{\theta_t}(x-\theta_b)f(x)\,dx$$
--   is concave on the section $\{\theta_b:(\theta_b,\theta_t)\in\Theta\}$ of the threshold domain (computed with $\alpha_b=0$).
--
--   In the proof of Proposition 3 this concavity reduces optimality of net terms ($\theta_b=0$) at $\alpha_b=0$ to a sign condition on $\partial\Pi_s/\partial\theta_b$ at $\theta_b=0$.
--
--   **Formalization Note** Concavity is Mathlib's `ConcaveOn`, which also asserts that the section is convex. The section is an interval $[0,\bar\theta]$: $C$ increases in $\theta_b$ (Lemma C.4), and $w_c$ decreases in $\theta_b$. $\Theta$ includes the constraints $\theta_t\le Q$ and $c\le w_c$ (image of §3.1's $c\le w_c\le w_t\le 1$ under (11)).
-- source:
--   Yang & Birge, Trade Credit, Risk Sharing, and Inventory Financing Portfolios, Management Science 64(8) (2018), accepted manuscript (LBS Research Online eprint 801), p. 42, Lemma C.8; used p. 37, proof of Proposition 3

import Mathlib
import Definitions.Def_TradeCredit_Terms_Model

namespace TradeCredit.Terms

theorem lemmaC8_concave_thetab (f : ℝ → ℝ) (hf : DemandModel f)
    (c αt K : ℝ) (hc0 : 0 < c) (hc1 : c < 1) (hαt0 : 0 ≤ αt) (hαt1 : αt ≤ 1) (hK : 0 < K) :
    ∀ θt : ℝ, ConcaveOn ℝ {θb : ℝ | (θb, θt) ∈ Theta f c 0 K} (fun θb => PiS f c 0 αt K θb θt) := by sorry

end TradeCredit.Terms
