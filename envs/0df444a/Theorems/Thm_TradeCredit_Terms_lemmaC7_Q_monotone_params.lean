-- Prove2me | Theorems.Thm_TradeCredit_Terms_lemmaC7_Q_monotone_params
-- name    : TradeCredit.Terms.lemmaC7_Q_monotone_params
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:09:38.464282+00:00
-- url     : https://prove2.me/theorems/fa660f62-6226-4d8e-ba80-a57ec7669525
-- title:
--   Lemma C.7, p. 42 — Q(θ_b, θ_t) increases in α_b and in K
-- statement:
--   Let the demand density $f$ satisfy the standing assumptions of §3, and fix thresholds $0\le\theta_b\le\theta_t$. Write $Q_{\alpha_b,K}(\theta_b,\theta_t)=\min\{q\ge 0: q\bar F(q)=[\theta_t+C_{\alpha_b,K}(\theta_b)]\bar F(\theta_t)\}$, showing the dependence of $C$ on $\alpha_b$ and $K$.
--   1. **In $\alpha_b$.** Let $K>0$ and $0\le a_1\le a_2\le 1$. Suppose $\hat F_b(\theta_b)>0$ for $\alpha_b=a_2$ and the defining equation of $Q_{a_2,K}$ has a nonnegative root. Then
--   $$Q_{a_1,K}(\theta_b,\theta_t)\le Q_{a_2,K}(\theta_b,\theta_t).$$
--   2. **In $K$.** Let $\alpha_b\in[0,1]$ with $\hat F_b(\theta_b)>0$, and let $0<K_1\le K_2$. Suppose the defining equation of $Q_{\alpha_b,K_2}$ has a nonnegative root. Then
--   $$Q_{\alpha_b,K_1}(\theta_b,\theta_t)\le Q_{\alpha_b,K_2}(\theta_b,\theta_t).$$
--
--   Costlier bank default and more retailer cash both raise the quantity induced by given thresholds. This is used in the proof of Proposition 3 (the condition (43) persists as $K$ grows) and of Proposition 6 (the supplier's optimal profit falls in $\alpha_b$).
--
--   **Formalization Note** $Q$ is defined as an infimum, which Lean sets to $0$ when there is no root. The lemma is therefore stated where the larger parameter's root set is nonempty, which is exactly when $Q$ is the paper's minimum. The smaller parameter then has a root too. $\hat F_b(\theta_b)>0$ keeps $C$ off its pole; it decreases in $\alpha_b$, so it holds for $a_1$ too. "Increases" is read weakly.
-- source:
--   Yang & Birge, Trade Credit, Risk Sharing, and Inventory Financing Portfolios, Management Science 64(8) (2018), accepted manuscript (LBS Research Online eprint 801), p. 42, Lemma C.7; used pp. 37 and 41

import Mathlib
import Definitions.Def_TradeCredit_Terms_Model

namespace TradeCredit.Terms

theorem lemmaC7_Q_monotone_params (f : ℝ → ℝ) (hf : DemandModel f)
    (θb θt : ℝ) (hθb : 0 ≤ θb) (hθbt : θb ≤ θt) :
    (∀ K : ℝ, 0 < K → ∀ a₁ a₂ : ℝ, 0 ≤ a₁ → a₁ ≤ a₂ → a₂ ≤ 1 → 0 < Fhatb f a₂ θb →
        (∃ q : ℝ, 0 ≤ q ∧ q * Fbar f q = (θt + Cfun f a₂ K θb) * Fbar f θt) →
        Qfun f a₁ K θb θt ≤ Qfun f a₂ K θb θt) ∧
      (∀ αb : ℝ, 0 ≤ αb → αb ≤ 1 → 0 < Fhatb f αb θb → ∀ K₁ K₂ : ℝ, 0 < K₁ → K₁ ≤ K₂ →
        (∃ q : ℝ, 0 ≤ q ∧ q * Fbar f q = (θt + Cfun f αb K₂ θb) * Fbar f θt) →
        Qfun f αb K₁ θb θt ≤ Qfun f αb K₂ θb θt) := by sorry

end TradeCredit.Terms
