-- Prove2me | Theorems.Thm_TradeCredit_Terms_lemmaC4_C_monotone
-- name    : TradeCredit.Terms.lemmaC4_C_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:09:28.489195+00:00
-- url     : https://prove2.me/theorems/8762c5a6-fe89-4e00-b2da-04ed79f6cf5b
-- title:
--   Lemma C.4, p. 42 — C(θ) is increasing in θ; if α_b = 0, C is convex
-- statement:
--   Let the demand density $f$ satisfy the standing assumptions of §3 (continuous, positive on $[0,\infty)$, IFR). Let $\alpha_b\in[0,1]$ and $K>0$, and let
--   $$C(\theta)=\frac{K+\int_0^\theta \hat F_b(x)\,dx}{\hat F_b(\theta)}-\theta,\qquad \hat F_b(x)=\bar F(x)[1-\alpha_b g(x)].$$
--   Then:
--   1. $C$ is (weakly) increasing on $\{\theta\ge 0:\ \hat F_b(\theta)>0\}$;
--   2. if $\alpha_b=0$, then $C$ is convex on $[0,\infty)$.
--
--   The monotonicity of $C$ is what makes the order quantity $Q(\theta_b,\theta_t)$ increase in $\theta_b$ (Corollary 3), and convexity at $\alpha_b=0$ drives the concavity of the supplier's profit in $\theta_b$ (Lemma C.8).
--
--   **Formalization Note** The printed lemma has no domain. $C$ has a pole where $\hat F_b$ vanishes, so monotonicity is stated on the set where $\hat F_b>0$. When $\alpha_b=0$, $\hat F_b=\bar F>0$ everywhere on $[0,\infty)$. "Increasing" is read weakly.
-- source:
--   Yang & Birge, Trade Credit, Risk Sharing, and Inventory Financing Portfolios, Management Science 64(8) (2018), accepted manuscript (LBS Research Online eprint 801), p. 42, Lemma C.4 (C(θ) from Proposition 1, p. 11)

import Mathlib
import Definitions.Def_TradeCredit_Terms_Model

namespace TradeCredit.Terms

theorem lemmaC4_C_monotone (f : ℝ → ℝ) (hf : DemandModel f)
    (αb K : ℝ) (hαb0 : 0 ≤ αb) (hαb1 : αb ≤ 1) (hK : 0 < K) :
    MonotoneOn (Cfun f αb K) {θ : ℝ | 0 ≤ θ ∧ 0 < Fhatb f αb θ} ∧
      (αb = 0 → ConvexOn ℝ (Set.Ici 0) (Cfun f αb K)) := by sorry

end TradeCredit.Terms
