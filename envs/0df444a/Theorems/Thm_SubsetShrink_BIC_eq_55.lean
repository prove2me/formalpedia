-- Prove2me | Theorems.Thm_SubsetShrink_BIC_eq_55
-- name    : SubsetShrink.BIC.eq_55
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T21:27:07.914071+00:00
-- url     : https://prove2.me/theorems/1df338c6-f068-44d1-bf1e-8c135cb74b2b
-- title:
--   (55), p. 50 — for b ≳ σ², high-probability bound on the error plus ℓ0 penalty of β̂^B_2
-- statement:
--   Work in the model $y=f^*+\epsilon$ with $\epsilon\sim N(0,\sigma^2I_n)$, $\sigma>0$, and a design $X\in\mathbb R^{n\times p}$ ($p\ge1$) with unit-norm columns. Let $a,b\ge0$ and let $\lambda_\beta,\mu_\beta$ be the penalties of §3.5.
--
--   There are universal constants $b_0$ and $C>0$ such that the following holds. If $b\ge b_0\sigma^2$, then for every $\epsilon_0\in(0,1)$ and every $\beta\in\mathbb R^p$, with probability at least $1-\epsilon_0$, every minimizer $\hat\beta$ of $\|y-X\beta\|^2+\lambda_\beta\|\beta\|+\mu_\beta\|\beta\|_0$ satisfies
--   $$\|f^*-X\hat\beta\|^2+\mu_{\hat\beta}\|\hat\beta\|_0\le C\Big(\|f^*-X\beta\|^2+\sigma^2\log(1/\epsilon_0)+\lambda_\beta\|\beta\|+\mu_\beta\|\beta\|_0\Big).$$
--
--   This is the case $b\gtrsim\sigma^2$ of the proof of Theorem 5: the $\ell_0$ penalty alone controls the noise, on the event of the union bound over model sizes.
--
--   **Formalization Note** "$\lesssim$" is a universal constant $C>0$ quantified before every other parameter; the page's threshold $b\ge 2c\sigma^2$ (with $c$ a universal constant of the proof) is the universal constant $b_0$. "With probability at least $1-\epsilon_0$" is the existence of a measurable set $A$ of noise vectors with $P(A)\ge1-\epsilon_0$ on which the inequality holds for every minimizer.
-- source:
--   Mazumder, Radchenko & Dedieu, Subset Selection with Shrinkage, arXiv:1708.03288v4, p. 50, proof of Theorem 5 (B.13), (55)

import Mathlib
import Definitions.Def_SubsetShrink_BIC_Model

namespace SubsetShrink.BIC

open MeasureTheory ProbabilityTheory

/-- (55), p. 50: in the case `b ≥ b0 σ²`, for each `ϵ0 ∈ (0, 1)` and each `β`, with probability
at least `1 − ϵ0`, every minimizer `β̂` of the objective of `β̂^B_2` satisfies
`‖f* − Xβ̂‖² + µ_β̂ ‖β̂‖₀ ≤ C (‖f* − Xβ‖² + σ² log(1/ϵ0) + λ_β ‖β‖ + µ_β ‖β‖₀)`. -/
theorem eq_55 :
    ∃ b0 C : ℝ, 0 < C ∧
      ∀ {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (fstar : Fin n → ℝ) (σ a b ϵ0 : ℝ)
        (β : Fin p → ℝ),
        SubsetShrink.Events.UnitCols X → 1 ≤ p → 0 < σ → 0 ≤ a → 0 ≤ b → b0 * σ ^ 2 ≤ b → 0 < ϵ0 → ϵ0 < 1 →
        ∃ A : Set (Fin n → ℝ), MeasurableSet A ∧ 1 - ϵ0 ≤ (SubsetShrink.Events.noiseLaw n σ A).toReal ∧
          ∀ ε ∈ A, ∀ βhat : Fin p → ℝ, IsBIC2 X (fstar + ε) a b βhat →
            ∑ i, (fstar i - X.mulVec βhat i) ^ 2 + muB b βhat * (SubsetShrink.Events.l0 βhat : ℝ) ≤
              C * (∑ i, (fstar i - X.mulVec β i) ^ 2 + σ ^ 2 * Real.log (1 / ϵ0) +
                lamB a β * SubsetShrink.Events.l2 β + muB b β * (SubsetShrink.Events.l0 β : ℝ)) := by sorry

end SubsetShrink.BIC
