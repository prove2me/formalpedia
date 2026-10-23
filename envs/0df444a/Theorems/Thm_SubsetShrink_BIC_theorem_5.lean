-- Prove2me | Theorems.Thm_SubsetShrink_BIC_theorem_5
-- name    : SubsetShrink.BIC.theorem_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T21:26:33.432591+00:00
-- url     : https://prove2.me/theorems/fa2971df-68af-492a-8944-1bfb46a540e0
-- title:
--   Theorem 5, p. 21 — oracle inequalities for the expected prediction error of the BIC-type estimators β̂^B_2 and β̂^B_1
-- statement:
--   Work in the model $y=f^*+\epsilon$, where $f^*\in\mathbb R^n$ is deterministic, $\epsilon$ has independent $N(0,\sigma^2)$ entries with $\sigma>0$, and the design $X\in\mathbb R^{n\times p}$ ($p\ge1$) has columns of unit Euclidean norm. For $a,b\ge0$ let $\lambda_\beta=a\sqrt{\|\beta\|_0\log(ep/\|\beta\|_0)}$ and $\mu_\beta=b\log(ep/\|\beta\|_0)$, and define the BIC-type estimators
--   $$\hat\beta^B_2\in\arg\min_\beta\ \|y-X\beta\|^2+\lambda_\beta\|\beta\|+\mu_\beta\|\beta\|_0,\qquad \hat\beta^B_1\in\arg\min_\beta\ \|y-X\beta\|^2+\lambda\|\beta\|_1+\mu_\beta\|\beta\|_0 .$$
--
--   There exist universal constants $a_0,b_0,c_0$ (and a universal constant $C>0$ implicit in $\lesssim$) such that:
--   1. if $a\ge a_0\sigma$ or $b\ge b_0\sigma^2$, then
--   $$\mathbb E\|f^*-X\hat\beta^B_2\|^2\le C\Big(\inf_{\beta\in\mathbb R^p}\big[\|f^*-X\beta\|^2+\lambda_\beta\|\beta\|+\mu_\beta\|\beta\|_0\big]+\sigma^2\Big);$$
--   2. if $\lambda\ge c_0\sigma\sqrt{\log(ep)}$ or $b\ge b_0\sigma^2$ (with $\lambda\ge 0$), then
--   $$\mathbb E\|f^*-X\hat\beta^B_1\|^2\le C\Big(\inf_{\beta\in\mathbb R^p}\big[\|f^*-X\beta\|^2+\lambda\|\beta\|_1+\mu_\beta\|\beta\|_0\big]+\sigma^2\Big).$$
--
--   The penalties choose the model size from the data, so these oracle inequalities hold over all of $\mathbb R^p$ rather than over a fixed sparsity class $B_0(k)$, and require no condition on the design beyond the normalization of its columns.
--
--   **Formalization Note** An estimator is a measurable map $\hat\beta:\mathbb R^n\to\mathbb R^p$ with $\hat\beta(y)$ a global minimizer of the objective for every $y$; the bound is claimed for every such selection (one exists; neither uniqueness nor a particular selection is assumed). The expectation is the lower Lebesgue integral of $\|f^*-X\hat\beta(f^*+\epsilon)\|^2$ against the law of $\epsilon$, so it cannot vanish by non-integrability. "$\lesssim$" is one universal constant $C>0$, chosen together with $a_0,b_0,c_0$ before $n,p,X,f^*,\sigma,a,b,\lambda$ and $\beta$; the infimum is written as "for every $\beta\in\mathbb R^p$". The page claims no sign for $a_0,b_0,c_0$, and none is stated; positivity is forced in any proof, since at $a=b=0$ the first bound fails for least squares. The paper's convention $0\cdot\infty=0$ makes $\lambda_0=\mu_0\|0\|_0=0$; the Lean products give the same value.
-- source:
--   Mazumder, Radchenko & Dedieu, Subset Selection with Shrinkage, arXiv:1708.03288v4, p. 21, Theorem 5; estimators p. 20, §3.5; proof B.13, pp. 49–51

import Mathlib
import Definitions.Def_SubsetShrink_BIC_Model

namespace SubsetShrink.BIC

open MeasureTheory ProbabilityTheory

/-- Theorem 5, p. 21: oracle inequalities for the expected prediction error of the BIC-type
estimators `β̂^B_2` and `β̂^B_1`, for every measurable selection of the minimizers. -/
theorem theorem_5 :
    ∃ a0 b0 c0 C : ℝ, 0 < C ∧
      (∀ {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (fstar : Fin n → ℝ) (σ a b : ℝ)
        (βhat : (Fin n → ℝ) → (Fin p → ℝ)),
        SubsetShrink.Events.UnitCols X → 1 ≤ p → 0 < σ → 0 ≤ a → 0 ≤ b → (a0 * σ ≤ a ∨ b0 * σ ^ 2 ≤ b) →
        Measurable βhat → (∀ y, IsBIC2 X y a b (βhat y)) →
        ∀ β : Fin p → ℝ,
          ∫⁻ ε, ENNReal.ofReal (∑ i, (fstar i - X.mulVec (βhat (fstar + ε)) i) ^ 2)
              ∂(SubsetShrink.Events.noiseLaw n σ) ≤
            ENNReal.ofReal (C * (∑ i, (fstar i - X.mulVec β i) ^ 2 + lamB a β * SubsetShrink.Events.l2 β +
              muB b β * (SubsetShrink.Events.l0 β : ℝ) + σ ^ 2))) ∧
      (∀ {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (fstar : Fin n → ℝ) (σ lam b : ℝ)
        (βhat : (Fin n → ℝ) → (Fin p → ℝ)),
        SubsetShrink.Events.UnitCols X → 1 ≤ p → 0 < σ → 0 ≤ lam → 0 ≤ b →
        (c0 * σ * Real.sqrt (Real.log (Real.exp 1 * p)) ≤ lam ∨ b0 * σ ^ 2 ≤ b) →
        Measurable βhat → (∀ y, IsBIC1 X y lam b (βhat y)) →
        ∀ β : Fin p → ℝ,
          ∫⁻ ε, ENNReal.ofReal (∑ i, (fstar i - X.mulVec (βhat (fstar + ε)) i) ^ 2)
              ∂(SubsetShrink.Events.noiseLaw n σ) ≤
            ENNReal.ofReal (C * (∑ i, (fstar i - X.mulVec β i) ^ 2 + lam * SubsetShrink.Events.l1 β +
              muB b β * (SubsetShrink.Events.l0 β : ℝ) + σ ^ 2))) := by sorry

end SubsetShrink.BIC
