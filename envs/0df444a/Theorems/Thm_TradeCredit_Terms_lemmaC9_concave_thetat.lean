-- Prove2me | Theorems.Thm_TradeCredit_Terms_lemmaC9_concave_thetat
-- name    : TradeCredit.Terms.lemmaC9_concave_thetat
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:09:59.364798+00:00
-- url     : https://prove2.me/theorems/353c7773-352d-4cc2-a5fc-c36128150ab2
-- title:
--   Lemma C.9, p. 42 — for every θ_b, Π_s is concave in θ_t
-- statement:
--   Let the demand density $f$ satisfy the standing assumptions of §3, and let $0<c<1$, $\alpha_b,\alpha_t\in[0,1]$ and $K>0$. For every $\theta_b$, the supplier's profit (8)
--   $$\theta_t\ \mapsto\ \Pi_s(\theta_b,\theta_t)$$
--   is concave on the section $\{\theta_t:(\theta_b,\theta_t)\in\Theta\}$ of the threshold domain.
--
--   Together with continuity, this concavity locates the optimal trade credit threshold $\theta_t^*$ in the proof of Proposition 3.
--
--   **Formalization Note** Concavity is Mathlib's `ConcaveOn`, which also asserts that the section is convex. The section is an interval: on it $[\theta_t+C(\theta_b)]\bar F(\theta_t)$ is increasing and $w_c$ is decreasing in $\theta_t$. $\Theta$ includes the constraints $\theta_t\le Q$ and $c\le w_c$ (image of §3.1's $c\le w_c\le w_t\le 1$ under (11)).
-- source:
--   Yang & Birge, Trade Credit, Risk Sharing, and Inventory Financing Portfolios, Management Science 64(8) (2018), accepted manuscript (LBS Research Online eprint 801), p. 42, Lemma C.9; used p. 38, proof of Proposition 3

import Mathlib
import Definitions.Def_TradeCredit_Terms_Model

namespace TradeCredit.Terms

theorem lemmaC9_concave_thetat (f : ℝ → ℝ) (hf : DemandModel f)
    (c αb αt K : ℝ) (hc0 : 0 < c) (hc1 : c < 1) (hαb0 : 0 ≤ αb) (hαb1 : αb ≤ 1)
    (hαt0 : 0 ≤ αt) (hαt1 : αt ≤ 1) (hK : 0 < K) :
    ∀ θb : ℝ, ConcaveOn ℝ {θt : ℝ | (θb, θt) ∈ Theta f c αb K}
      (fun θt => PiS f c αb αt K θb θt) := by sorry

end TradeCredit.Terms
