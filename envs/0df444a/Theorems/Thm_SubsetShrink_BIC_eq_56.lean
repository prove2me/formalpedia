-- Prove2me | Theorems.Thm_SubsetShrink_BIC_eq_56
-- name    : SubsetShrink.BIC.eq_56
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T21:26:49.949103+00:00
-- url     : https://prove2.me/theorems/165454dc-82a0-4996-b687-69f99f5ab3d4
-- title:
--   (56), p. 50 — if a ≳ σ or b ≳ σ², a high-probability oracle inequality for β̂^B_2
-- statement:
--   Work in the model $y=f^*+\epsilon$ with $\epsilon\sim N(0,\sigma^2I_n)$, $\sigma>0$, and a design $X\in\mathbb R^{n\times p}$ ($p\ge1$) with unit-norm columns. Let $a,b\ge0$ and let $\lambda_\beta,\mu_\beta$ be the penalties of §3.5.
--
--   There are universal constants $a_0,b_0$ and $C>0$ such that, if $a\ge a_0\sigma$ or $b\ge b_0\sigma^2$, then for every $\delta_0\in(0,1)$, with probability at least $1-\delta_0$, every minimizer $\hat\beta$ of $\|y-X\beta\|^2+\lambda_\beta\|\beta\|+\mu_\beta\|\beta\|_0$ satisfies
--   $$\|f^*-X\hat\beta\|^2+\mu_{\hat\beta}\|\hat\beta\|_0\le C\Big(\inf_{\beta\in\mathbb R^p}\big[\|f^*-X\beta\|^2+\lambda_\beta\|\beta\|+\mu_\beta\|\beta\|_0\big]+\sigma^2\log(1/\delta_0)\Big).$$
--
--   This combines the two cases (54) and (55) and is the high-probability form of the first bound of Theorem 5.
--
--   **Formalization Note** The infimum is encoded as "for every $\beta\in\mathbb R^p$" (equivalent for a fixed $C$, and free of real-infimum junk values); the event is chosen before $\beta$, so one event of probability $\ge1-\delta_0$ serves all $\beta$ at once, as the infimum inside the probability requires. "$\lesssim$" is a universal constant $C>0$ quantified before every other parameter.
-- source:
--   Mazumder, Radchenko & Dedieu, Subset Selection with Shrinkage, arXiv:1708.03288v4, p. 50, proof of Theorem 5 (B.13), (56)

import Mathlib
import Definitions.Def_SubsetShrink_BIC_Model

namespace SubsetShrink.BIC

open MeasureTheory ProbabilityTheory

/-- (56), p. 50: if `a ≥ a0 σ` or `b ≥ b0 σ²`, then for each `δ0 ∈ (0, 1)` there is an event of
probability at least `1 − δ0` on which every minimizer `β̂` of the objective of `β̂^B_2` satisfies,
simultaneously for all `β ∈ ℝ^p`,
`‖f* − Xβ̂‖² + µ_β̂ ‖β̂‖₀ ≤ C (‖f* − Xβ‖² + λ_β ‖β‖ + µ_β ‖β‖₀ + σ² log(1/δ0))`. -/
theorem eq_56 :
    ∃ a0 b0 C : ℝ, 0 < C ∧
      ∀ {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (fstar : Fin n → ℝ) (σ a b δ0 : ℝ),
        SubsetShrink.Events.UnitCols X → 1 ≤ p → 0 < σ → 0 ≤ a → 0 ≤ b → (a0 * σ ≤ a ∨ b0 * σ ^ 2 ≤ b) →
        0 < δ0 → δ0 < 1 →
        ∃ A : Set (Fin n → ℝ), MeasurableSet A ∧ 1 - δ0 ≤ (SubsetShrink.Events.noiseLaw n σ A).toReal ∧
          ∀ ε ∈ A, ∀ βhat : Fin p → ℝ, IsBIC2 X (fstar + ε) a b βhat →
            ∀ β : Fin p → ℝ,
              ∑ i, (fstar i - X.mulVec βhat i) ^ 2 + muB b βhat * (SubsetShrink.Events.l0 βhat : ℝ) ≤
                C * (∑ i, (fstar i - X.mulVec β i) ^ 2 + lamB a β * SubsetShrink.Events.l2 β +
                  muB b β * (SubsetShrink.Events.l0 β : ℝ) + σ ^ 2 * Real.log (1 / δ0)) := by sorry

end SubsetShrink.BIC
