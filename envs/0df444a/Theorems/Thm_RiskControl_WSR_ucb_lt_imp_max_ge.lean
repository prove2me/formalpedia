-- Prove2me | Theorems.Thm_RiskControl_WSR_ucb_lt_imp_max_ge
-- name    : RiskControl.WSR.ucb_lt_imp_max_ge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:36:48.660921+00:00
-- url     : https://prove2.me/theorems/6d36424c-6094-4a57-980d-9408f2b57e04
-- title:
--   Proof of Proposition 5, p. 26 (corrected) — if R̂⁺_WSR < R then maxᵢ 𝒦ᵢ(R) ≥ 1/δ
-- statement:
--   Let $n \in \mathbb N$, $\delta \in \mathbb R$, let $\omega = (L_1, \dots, L_n)$ be a sample with every $L_j \in [0,1]$, and let $R \ge 0$. If $\widehat R^+_{\mathrm{WSR}} < R$, then
--   $$\max_{i=1,\dots,n} \mathcal K_i(R) \ge \frac1\delta,$$
--   that is, $\mathcal K_i(R) \ge 1/\delta$ for some $i \in \{1, \dots, n\}$ (see the definition `RiskControl.WSR.Process` for $\mathcal K_i$ and $\widehat R^+_{\mathrm{WSR}}$).
--
--   Applied at the true mean $R = R(\lambda)$, this places the failure event $\{\widehat R^+_{\mathrm{WSR}} < R(\lambda)\}$ inside the event controlled by Ville's inequality.
--
--   **Formalization Note** The paper writes "if $\widehat R^+_{\mathrm{WSR}}(\lambda) < R(\lambda)$, then $P(\max_{i=1,\dots,n}\mathcal K_i \ge 1/\delta)$", with a stray "$P($"; the intended claim, stated here, is the event $\max_i \mathcal K_i(R) \ge 1/\delta$. The comparison $\widehat R^+_{\mathrm{WSR}} < R$ is in the extended reals. The hypothesis $R \ge 0$ holds for the paper's $R = R(\lambda)$, the mean of a nonnegative loss.
-- source:
--   Bates, Angelopoulos, Lei, Malik & Jordan, arXiv:2101.02703v3, Proof of Proposition 5, p. 26, last sentence before the third display

import Mathlib
import Definitions.Def_RiskControl_WSR_Process

namespace RiskControl.WSR

/-- Proof of Proposition 5, p. 26 (arXiv:2101.02703v3), with the page's stray `P(` removed: for
a sample of losses in `[0, 1]` and `R ≥ 0`, if `R̂⁺_WSR < R` then `max_{i=1,…,n} 𝒦_i(R; λ) ≥ 1/δ`. -/
theorem ucb_lt_imp_max_ge (n : ℕ) (δ : ℝ) (ω : Fin n → ℝ)
    (hω : ∀ j, ω j ∈ Set.Icc (0 : ℝ) 1) (R : ℝ) (hR : 0 ≤ R) :
    wsrUCB n δ ω < (R : EReal) → ∃ i ∈ Finset.Icc 1 n, 1 / δ ≤ K n δ ω i R := by sorry

end RiskControl.WSR
