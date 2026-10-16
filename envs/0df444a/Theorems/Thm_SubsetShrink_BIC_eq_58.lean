-- Prove2me | Theorems.Thm_SubsetShrink_BIC_eq_58
-- name    : SubsetShrink.BIC.eq_58
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T21:26:47.647371+00:00
-- url     : https://prove2.me/theorems/cdf854f8-e259-45d5-aff5-0455d5d76b05
-- title:
--   (58), pp. 50–51 — if λ ≳ σ√log(ep) or b ≳ σ², a high-probability oracle inequality for β̂^B_1
-- statement:
--   Work in the model $y=f^*+\epsilon$ with $\epsilon\sim N(0,\sigma^2I_n)$, $\sigma>0$, and a design $X\in\mathbb R^{n\times p}$ ($p\ge1$) with unit-norm columns. Let $\lambda,b\ge0$ and $\mu_\beta=b\log(ep/\|\beta\|_0)$.
--
--   There are universal constants $c_0,b_0$ and $C>0$ such that, if $\lambda\ge c_0\sigma\sqrt{\log(ep)}$ or $b\ge b_0\sigma^2$, then for every $\delta_0\in(0,1)$, with probability at least $1-\delta_0$, every minimizer $\hat\beta$ of $\|y-X\beta\|^2+\lambda\|\beta\|_1+\mu_\beta\|\beta\|_0$ satisfies
--   $$\|f^*-X\hat\beta\|^2+\mu_{\hat\beta}\|\hat\beta\|_0\le C\Big(\inf_{\beta\in\mathbb R^p}\big[\|f^*-X\beta\|^2+\lambda\|\beta\|_1+\mu_\beta\|\beta\|_0\big]+\sigma^2\log(1/\delta_0)\Big).$$
--
--   This is the high-probability form of the second bound of Theorem 5.
--
--   **Formalization Note** The page derives (58) in the case $b\gtrsim\sigma^2$ (p. 50) and extends it to the case $\lambda\ge c_0\sigma\sqrt{\log(ep)}$ (p. 51); the statement covers both. The infimum is encoded as "for every $\beta$", with the event chosen before $\beta$. "$\lesssim$" is a universal constant $C>0$ quantified before every other parameter.
-- source:
--   Mazumder, Radchenko & Dedieu, Subset Selection with Shrinkage, arXiv:1708.03288v4, pp. 50–51, proof of Theorem 5 (B.13), (58) and the paragraph after it

import Mathlib
import Definitions.Def_SubsetShrink_BIC_Model

namespace SubsetShrink.BIC

open MeasureTheory ProbabilityTheory

/-- (58), pp. 50–51: if `λ ≥ c0 σ √log(ep)` or `b ≥ b0 σ²`, then for each `δ0 ∈ (0, 1)` there is
an event of probability at least `1 − δ0` on which every minimizer `β̂` of the objective of
`β̂^B_1` satisfies, simultaneously for all `β ∈ ℝ^p`,
`‖f* − Xβ̂‖² + µ_β̂ ‖β̂‖₀ ≤ C (‖f* − Xβ‖² + λ ‖β‖₁ + µ_β ‖β‖₀ + σ² log(1/δ0))`. -/
theorem eq_58 :
    ∃ c0 b0 C : ℝ, 0 < C ∧
      ∀ {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (fstar : Fin n → ℝ) (σ lam b δ0 : ℝ),
        SubsetShrink.Events.UnitCols X → 1 ≤ p → 0 < σ → 0 ≤ lam → 0 ≤ b →
        (c0 * σ * Real.sqrt (Real.log (Real.exp 1 * p)) ≤ lam ∨ b0 * σ ^ 2 ≤ b) →
        0 < δ0 → δ0 < 1 →
        ∃ A : Set (Fin n → ℝ), MeasurableSet A ∧ 1 - δ0 ≤ (SubsetShrink.Events.noiseLaw n σ A).toReal ∧
          ∀ ε ∈ A, ∀ βhat : Fin p → ℝ, IsBIC1 X (fstar + ε) lam b βhat →
            ∀ β : Fin p → ℝ,
              ∑ i, (fstar i - X.mulVec βhat i) ^ 2 + muB b βhat * (SubsetShrink.Events.l0 βhat : ℝ) ≤
                C * (∑ i, (fstar i - X.mulVec β i) ^ 2 + lam * SubsetShrink.Events.l1 β +
                  muB b β * (SubsetShrink.Events.l0 β : ℝ) + σ ^ 2 * Real.log (1 / δ0)) := by sorry

end SubsetShrink.BIC
