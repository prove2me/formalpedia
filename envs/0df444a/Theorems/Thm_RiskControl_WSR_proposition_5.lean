-- Prove2me | Theorems.Thm_RiskControl_WSR_proposition_5
-- name    : RiskControl.WSR.proposition_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:36:01.154559+00:00
-- url     : https://prove2.me/theorems/2844dd0d-8071-490e-baef-ded586b85a50
-- title:
--   Proposition 5, p. 7 — the Waudby-Smith–Ramdas bound R̂⁺_WSR is a (1 − δ) upper confidence bound for the mean loss
-- statement:
--   This is Proposition 5 of Bates, Angelopoulos, Lei, Malik and Jordan (the Waudby-Smith–Ramdas bound), for one fixed parameter $\lambda$.
--
--   Let $Q$ be a probability measure on $\mathbb R$ concentrated on $[0,1]$, the law of the loss $L(Y, \mathcal T_\lambda(X))$, and let $R = \int x\, dQ(x)$ be its mean, the risk $R(\lambda)$. Let $n \ge 1$, let $\delta \in (0,1)$, and let $L_1, \dots, L_n$ be i.i.d. with law $Q$ (the losses of the calibration points). With $\widehat R^+_{\mathrm{WSR}}$ the bound of Proposition 5 computed from $L_1, \dots, L_n$ (see the definition `RiskControl.WSR.Process`),
--   $$\mathbb P\bigl(\widehat R^+_{\mathrm{WSR}} < R\bigr) \le \delta, \qquad\text{equivalently}\qquad \mathbb P\bigl(R \le \widehat R^+_{\mathrm{WSR}}\bigr) \ge 1 - \delta.$$
--
--   That is, $\widehat R^+_{\mathrm{WSR}}$ is a $(1-\delta)$ upper confidence bound for $R(\lambda)$ in the sense of display (3) of the paper. Combined with the paper's Theorem 1, it yields Theorem 4: UCB calibration with this bound gives a risk-controlling prediction set.
--
--   **Formalization Note** $\lambda$ is fixed and dropped from the notation: $Q$ is the law of $L(Y, \mathcal T_\lambda(X))$, which lies in $[0,1]$ by the standing assumption of §3.1 (loss nonnegative and bounded by one), so the calibration losses are i.i.d. with law $Q$ and the probability is the product measure $Q^{\otimes n}$ on $\mathbb R^n$. The statement bounds the failure event $\{\widehat R^+_{\mathrm{WSR}} < R\}$ by $\delta$; it is evaluated by the outer measure, which for a measurable event is the page's $P(R \le \widehat R^+_{\mathrm{WSR}}) \ge 1 - \delta$. Two hypotheses implicit on the page are added: $n \ge 1$ ($n$ is the sample size and appears in a denominator of $\nu_i$) and $0 < \delta < 1$ (so that $\log(1/\delta) > 0$; for $\delta \ge 1$ the claim is trivial). The infimum defining $\widehat R^+_{\mathrm{WSR}}$ is taken in the extended reals, so it is $+\infty$ (and the bound holds) when no $R \ge 0$ qualifies.
-- source:
--   Bates, Angelopoulos, Lei, Malik & Jordan, arXiv:2101.02703v3, Proposition 5, p. 7; proof p. 26

import Mathlib
import Definitions.Def_RiskControl_WSR_Process

open MeasureTheory

namespace RiskControl.WSR

/-- Proposition 5 (Waudby-Smith–Ramdas bound), p. 7 (arXiv:2101.02703v3): for `n ≥ 1` i.i.d.
losses with law `Q` on `[0, 1]` and `δ ∈ (0, 1)`, `R̂⁺_WSR` is a `(1 − δ)` upper confidence
bound for the mean `R = ∫ x dQ`: `Qⁿ(R̂⁺_WSR < R) ≤ δ`. -/
theorem proposition_5 (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hQ : ∀ᵐ x ∂Q, x ∈ Set.Icc (0 : ℝ) 1) (n : ℕ) (hn : 1 ≤ n)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (Measure.pi fun _ : Fin n => Q)
        {ω | wsrUCB n δ ω < ((∫ x, x ∂Q : ℝ) : EReal)} ≤ ENNReal.ofReal δ := by sorry

end RiskControl.WSR
