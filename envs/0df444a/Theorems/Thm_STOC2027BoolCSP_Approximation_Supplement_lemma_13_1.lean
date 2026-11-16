-- Prove2me | Theorems.Thm_STOC2027BoolCSP_Approximation_Supplement_lemma_13_1
-- name    : STOC2027BoolCSP.Approximation.Supplement.lemma_13_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:36:37.084834+00:00
-- url     : https://prove2.me/theorems/84fec2e5-9cc0-498e-9402-a62bdbb124b5
-- title:
--   Lemma 13.1 — uniform common-function transfer from Gaussian to Boolean acceptance
-- statement:
--   Let $k\ge0$ and let $\mu_b$, $b$ in a finite set $B$, be laws on $\{-1,1\}^k$ with uniform one-bit marginals, $\Pr_{\mu_b}[X_j=1]=1/2$, and every atom at least $\alpha_*>0$. Let $p_b\ge0$, $\sum_bp_b=1$, be branch weights, $\Sigma_b=\mathbb E_{\mu_b}XX^{\mathsf T}$ and $\beta\in\mathbb R$. Suppose that for every dimension $N$ and every measurable $f:\mathbb R^N\to\mathbb R$ with $|f|\le1$ that is odd almost everywhere,
--   $$\sum_b p_b\,2^{-k}\,\mathbb E_{\Sigma_b}\prod_{j=1}^k\big(1+f(G_j)\big)\le\beta,$$
--   the $N$ columns of $(G_1,\dots,G_k)$ being independent $N(0,\Sigma_b)$ vectors. Then for every $\varepsilon>0$ there are $\eta,\tau>0$, independent of $R$, such that for every $R$ and every folded $h:\{-1,1\}^R\to[0,1]$ with
--   $$\max_i\ \mathrm{Inf}_i(T_{1-\eta}h)\le\tau,$$
--   the Boolean global-branch acceptance satisfies
--   $$\sum_b p_b\,\mathbb E\prod_{j=1}^k h(X_j)\le\beta+\varepsilon,$$
--   where, given $b$, the $R$ columns of $X$ are independent draws from $\mu_b$ and $X_1,\dots,X_k$ are its rows.
--
--   Section 14 applies the lemma to the two regularized laws (61) with weights $1-a$, $a$ and the Gaussian bound $\beta$ of (62).
--
--   Differences from the source:
--   - reading: fixed branch weights p_b; one first chooses b → p_b ≥ 0 with Σ_b p_b = 1; reason: the branch is drawn with probability p_b
--   - encoding: laws on {−1,1}^k with uniform one-bit marginals → atom masses μ_b(x) summing to one with Σ_{x : x_j = +1} μ_b(x) = 1/2 for every j; reason: a finite law is its mass function
--   - encoding: max_i Inf_i(T_{1−η} h) ≤ τ → Inf_i(T_{1−η} h) ≤ τ for every i; reason: the same condition; vacuous for R = 0
--   - encoding: common measurable odd f with |f| ≤ 1 in every finite dimension → ∀ N, measurable f : ℝ^N → ℝ with |f| ≤ 1 everywhere and f(−z) = −f(z) Lebesgue-a.e.; columns multivariateGaussian 0 Σ_b; reason: Section 12's oddness convention; Σ_b is positive semidefinite, possibly singular
-- source:
--   Zhijie Zheng, Yucong He, Chengzhi Xie, Approximation and Even Arity Hardness for Boolean Constraint Satisfaction, STOC 2027 submission #40 (October 2026), printed p. 28 (PDF 31), Lemma 13.1 with the notation of the Section 13 preamble; proof printed p. 28–30 (PDF 31–33)

import Mathlib
import Definitions.Def_STOC2027BoolCSP_Approximation_Instance
import Definitions.Def_STOC2027BoolCSP_Approximation_Supplement_TwoHub
import Definitions.Def_STOC2027BoolCSP_Approximation_Supplement_BoolFourier

namespace STOC2027BoolCSP.Approximation.Supplement

open MeasureTheory ProbabilityTheory STOC2027BoolCSP.Approximation

/-- Lemma 13.1 (uniform common-function transfer), printed p. 28. Let `µ_b` (`b ∈ B`, finite) be
laws on `{−1,1}^k` with uniform one-bit marginals and every atom at least `α* > 0`, let `p_b` be
branch weights and `Σ_b = E_{µ_b} X Xᵀ`. If for every dimension `N` and every measurable `f` with
`|f| ≤ 1`, odd almost everywhere, `Σ_b p_b 2^{−k} E_{Σ_b} Π_j (1 + f(G_j)) ≤ β`, then for every
`ε > 0` there are `η, τ > 0`, chosen before `R`, such that every folded `h : {−1,1}^R → [0,1]` with
`max_i Inf_i(T_{1−η} h) ≤ τ` has Boolean global-branch acceptance at most `β + ε`. -/
theorem lemma_13_1 (k : ℕ) {B : Type*} [Fintype B] (μ : B → (Fin k → Bool) → ℝ)
    (αs : ℝ) (hαs : 0 < αs) (hatom : ∀ b x, αs ≤ μ b x) (hsum : ∀ b, ∑ x, μ b x = 1)
    (hmarg : ∀ b j, ∑ x ∈ Finset.univ.filter (fun x : Fin k → Bool => x j = true), μ b x = 1 / 2)
    (p : B → ℝ) (hp : ∀ b, 0 ≤ p b) (hpsum : ∑ b, p b = 1) (β : ℝ)
    (hgauss : ∀ (N : ℕ) (f : (Fin N → ℝ) → ℝ), Measurable f → (∀ z, |f z| ≤ 1) →
      (∀ᵐ z ∂(volume : Measure (Fin N → ℝ)), f (-z) = -f z) →
      ∑ b, p b * gaussAcc (secondMoment (μ b)) f ≤ β) :
    ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ τ : ℝ, 0 < τ ∧
      ∀ (R : ℕ) (h : (Fin R → Bool) → ℝ), (∀ z, 0 ≤ h z ∧ h z ≤ 1) → IsFolded h →
        (∀ i, influence (noiseOp (1 - η) h) i ≤ τ) →
        boolAcc μ p h ≤ β + ε := by sorry

end STOC2027BoolCSP.Approximation.Supplement
