-- Prove2me | Theorems.Thm_SubsetShrink_BIC_eq_54
-- name    : SubsetShrink.BIC.eq_54
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T21:26:38.656233+00:00
-- url     : https://prove2.me/theorems/1024b622-5a15-4efb-93f1-63bb1d103776
-- title:
--   (54), p. 49 — for a ≳ σ, high-probability bound on the error plus ℓ0 penalty of β̂^B_2
-- statement:
--   Work in the model $y=f^*+\epsilon$ with $\epsilon\sim N(0,\sigma^2I_n)$, $\sigma>0$, and a design $X\in\mathbb R^{n\times p}$ ($p\ge1$) with unit-norm columns. Let $a,b\ge 0$ and let $\lambda_\beta,\mu_\beta$ be the penalties of §3.5.
--
--   There are universal constants $a_0$ and $C>0$ such that the following holds. If $a\ge a_0\sigma$, then for every $\delta_0\in(0,1)$ and every $\beta\in\mathbb R^p$, with probability at least $1-\delta_0/2$, every minimizer $\hat\beta$ of $\|y-X\beta\|^2+\lambda_\beta\|\beta\|+\mu_\beta\|\beta\|_0$ satisfies
--   $$\|f^*-X\hat\beta\|^2+\mu_{\hat\beta}\|\hat\beta\|_0\le C\Big(\|f^*-X\beta\|^2+\lambda_\beta\|\beta\|+\sigma^2\log(1/\delta_0)+\mu_\beta\|\beta\|_0\Big).$$
--
--   This is the case $a\gtrsim\sigma$ of the proof of Theorem 5: the $\ell_2$ penalty alone controls the noise.
--
--   **Formalization Note** "$\lesssim$" is a universal constant $C>0$ quantified before $n,p,X,f^*,\sigma,a,b,\delta_0,\beta$; "with probability at least $1-\delta_0/2$" is the existence of a measurable set $A$ of noise vectors with $P(A)\ge1-\delta_0/2$ on which the inequality holds for every minimizer. The constant $a_0$ carries no sign claim, as on the page.
-- source:
--   Mazumder, Radchenko & Dedieu, Subset Selection with Shrinkage, arXiv:1708.03288v4, p. 49, proof of Theorem 5 (B.13), (54)

import Mathlib
import Definitions.Def_SubsetShrink_BIC_Model

namespace SubsetShrink.BIC

open MeasureTheory ProbabilityTheory

/-- (54), p. 49: in the case `a ≥ a0 σ`, for each `δ0 ∈ (0, 1)` and each `β`, with probability
at least `1 − δ0/2`, every minimizer `β̂` of the objective of `β̂^B_2` satisfies
`‖f* − Xβ̂‖² + µ_β̂ ‖β̂‖₀ ≤ C (‖f* − Xβ‖² + λ_β ‖β‖ + σ² log(1/δ0) + µ_β ‖β‖₀)`. -/
theorem eq_54 :
    ∃ a0 C : ℝ, 0 < C ∧
      ∀ {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (fstar : Fin n → ℝ) (σ a b δ0 : ℝ)
        (β : Fin p → ℝ),
        SubsetShrink.Events.UnitCols X → 1 ≤ p → 0 < σ → 0 ≤ a → 0 ≤ b → a0 * σ ≤ a → 0 < δ0 → δ0 < 1 →
        ∃ A : Set (Fin n → ℝ), MeasurableSet A ∧ 1 - δ0 / 2 ≤ (SubsetShrink.Events.noiseLaw n σ A).toReal ∧
          ∀ ε ∈ A, ∀ βhat : Fin p → ℝ, IsBIC2 X (fstar + ε) a b βhat →
            ∑ i, (fstar i - X.mulVec βhat i) ^ 2 + muB b βhat * (SubsetShrink.Events.l0 βhat : ℝ) ≤
              C * (∑ i, (fstar i - X.mulVec β i) ^ 2 + lamB a β * SubsetShrink.Events.l2 β +
                σ ^ 2 * Real.log (1 / δ0) + muB b β * (SubsetShrink.Events.l0 β : ℝ)) := by sorry

end SubsetShrink.BIC
