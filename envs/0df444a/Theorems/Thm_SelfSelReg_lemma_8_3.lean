-- Prove2me | Theorems.Thm_SelfSelReg_lemma_8_3
-- name    : SelfSelReg.lemma_8_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:49:00.208847+00:00
-- url     : https://prove2.me/theorems/17fa59e6-ff1d-4200-abd7-64aefe25a711
-- title:
--   Lemma 8.3 — peeling-weight stability $|\mathbb E[\psi(\hat\omega_{\hat R}-\omega_R)]|\le\frac1{\sqrt{2\pi}}\|\psi\|_{L^2}(\sum\|\hat w-w_{\mathrm{match}(\hat w)}\|_2^2)^{1/2}$
-- statement:
--   In the Gaussian self-selection model ($n\ge1$, $2\le k\le n$), fix a set $R\subsetneq[k]$ and a list $\hat R$ of vectors of $\mathbb R^n$ with a bijection $\mathrm{match}:\hat R\to R$. Let $X'\sim N(0,I_n)$ be independent of the covariate and noises. For every measurable $\psi:\mathbb R^n\times\mathbb R^n\to\mathbb R$ with $\|\psi\|_{L^2(X,X')}=(\mathbb E|\psi(X,X')|^2)^{1/2}<\infty$,
--   $$\Big|\mathbb E_{X,Y_{\max},X'}\big[\psi(X,X')\big(\hat\omega_{\hat R}(X,Y_{\max})-\omega_R(X,Y_{\max})\big)\big]\Big|\le\frac1{\sqrt{2\pi}}\|\psi\|_{L^2(X,X')}\Big(\sum_{\hat w\in\hat R}\|\hat w-w_{\mathrm{match}(\hat w)}\|_2^2\Big)^{1/2}.$$
--   Here $\omega_R$ and $\hat\omega_{\hat R}$ are the ideal and estimated signed peeling weights at threshold $T$.
--
--   Replacing the recovered regressors by their estimates in the peeling weight changes any weighted expectation by at most the estimation error; this is the "error from recovered regressors" term of the decomposition (111).
--
--   **Formalization Note** The recovered list is a family $\hat w$ read on $R$. The expectation is over $(X,\xi)$ and an independent $X'$, with $Y_{\max}$ computed from $(X,\xi)$.
--
--   Differences from the source:
--   - generalization: T is the hyperparameter of Hyperparameters 4.1 → every real T; reason: the bound holds for every threshold and specializes to the hyperparameter
--   - encoding: a list R̂ with a bijection match : R̂ → R → a family ŵ : [k] → ℝⁿ read on R, the estimate matched to i ∈ R being ŵ_i; reason: a list matched bijectively to R is the same as an R-indexed family
--   - encoding: ‖ψ‖_{L²(X,X′)} < ∞ and E_{X,Y_max,X′} → MemLp ψ 2 under N(0, I_n) ⊗ N(0, I_n), and the integral over (X, ξ) ⊗ X′ with Y_max = max_i Y_i; reason: same quantities
-- source:
--   Zhou, Linear Regression with Self-Selection Bias in Polynomial Time, STOC 2027 submission (manuscript sha256 5d65f750…), Lemma 8.3, (113), p.58 (PDF p.61); proof §8.3, pp.61–62 (PDF pp.64–65)

import Mathlib
import Definitions.Def_SelfSelReg_jointLaw
import Definitions.Def_SelfSelReg_peelWeight

open MeasureTheory ProbabilityTheory

namespace SelfSelReg

/-- **Lemma 8.3** (Peeling-Weight Stability).

F. Zhou, *Linear Regression with Self-Selection Bias in Polynomial Time*, STOC 2027 submission
(manuscript sha256 5d65f750…), Lemma 8.3, p.58 (PDF p.61): "Consider the Gaussian self-selection model
(Definition 1.1). Fix a list R̂ of vectors in ℝⁿ, a set R ⊊ [k], and a bijection match : R̂ → R. Let
X′ ∼ N(0, I_n) be independent of the covariate and noises. For every measurable function
ψ : ℝⁿ × ℝⁿ → ℝ with ‖ψ‖_{L²(X,X′)} < ∞,
|E_{X,Y_max,X′}[ψ(X, X′)(ω̂_R̂(X, Y_max) − ω_R(X, Y_max))]| ≤ (1/√(2π)) ‖ψ‖_{L²(X,X′)}
(Σ_{ŵ∈R̂} ‖ŵ − w_match(ŵ)‖₂²)^{1/2}." (113)

**Formalization Note.**
* The list `R̂` with its bijection to `R` is a family `ŵ` read on `R` (the estimate matched to `i` is
  `ŵ_i`); `ω_R = peelWeight T w R` (104), `ω̂_R̂ = peelWeight T ŵ R` (106).
* The expectation is over `(X, ξ) ∼ jointLaw` and an independent `X′ ∼ N(0, I_n)`, with
  `Y_max = yMax w X ξ`. `‖ψ‖_{L²(X,X′)} = (E|ψ(X, X′)|²)^{1/2}` (p.58) under `N(0, I_n) ⊗ N(0, I_n)`;
  "`< ∞`" is `MemLp ψ 2`.
* `T` is the threshold used in `ω`, fixed in the paper by Hyperparameters 4.1; the statement is for
  every real `T` (a generalization). No assumption on `w` (none on the page). -/
theorem lemma_8_3 (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (hkn : k ≤ n)
    (w ŵ : Fin k → EuclideanSpace ℝ (Fin n)) (T : ℝ) (R : Finset (Fin k)) (hR : R ≠ Finset.univ)
    (ψ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → ℝ) (hψm : Measurable ψ)
    (hψ : MemLp ψ 2 ((stdGaussian (EuclideanSpace ℝ (Fin n))).prod
      (stdGaussian (EuclideanSpace ℝ (Fin n))))) :
    |∫ p, ψ (p.1.1, p.2) *
        (peelWeight T ŵ R p.1.1 (yMax w p.1.1 p.1.2) - peelWeight T w R p.1.1 (yMax w p.1.1 p.1.2))
        ∂((jointLaw n k).prod (stdGaussian (EuclideanSpace ℝ (Fin n))))| ≤
      1 / Real.sqrt (2 * Real.pi) *
        Real.sqrt (∫ p, ψ p ^ 2 ∂((stdGaussian (EuclideanSpace ℝ (Fin n))).prod
          (stdGaussian (EuclideanSpace ℝ (Fin n))))) *
        Real.sqrt (∑ i ∈ R, ‖ŵ i - w i‖ ^ 2) := by sorry

end SelfSelReg
