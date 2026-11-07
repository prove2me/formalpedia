-- Prove2me | Theorems.Thm_SelfSelReg_lemma_8_8
-- name    : SelfSelReg.lemma_8_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:48:56.320111+00:00
-- url     : https://prove2.me/theorems/699456f9-200b-4789-9053-445961ec37bc
-- title:
--   Lemma 8.8 — pairwise exceedance bound $\mathbb E[|\psi|\mathbf 1\{Y_i>T,Y_j>T\}]\le e^{4s\log K-T^2/(2K)}\|\psi\|_{L^2}\lambda_j^{(2r)}$
-- statement:
--   In the Gaussian self-selection model ($n\ge1$, $2\le k\le n$) under Assumption 1.2 with constants $B\ge1$, $\Delta\in(0,1]$, let $K=16(1+B^2)^3/\Delta^4$, let $s\ge1$ be an integer and $T>0$ with $T^2\ge Ks$. Let $X'\sim N(0,I_n)$ be independent of the covariate and the noises, and let $\psi(X,X')$ be a real polynomial of degree at most $2s+1$. For every pair of distinct indices $i,j\in[k]$ and every $1\le r\le s$,
--   $$\mathbb E_{X,\xi_i,\xi_j,X'}\big[|\psi(X,X')|\,\mathbf 1\{Y_i>T,\,Y_j>T\}\big]\le e^{4s\log K-T^2/(2K)}\,\|\psi\|_{L^2(X,X')}\,\lambda_j^{(2r)} .$$
--
--   Two responses rarely exceed the threshold together, even against a polynomial weight; summing this over pairs gives the peeling bias bound, Lemma 8.4(ii).
--
--   **Formalization Note** $\psi$ is a multivariate polynomial in the $2n$ coordinates of $(X,X')$ with total degree at most $2s+1$. The expectation is over all noises (the integrand depends only on $\xi_i,\xi_j$). Natural logarithm.
--
--   Differences from the source:
--   - encoding: a real polynomial ψ(X, X′) of degree at most 2s + 1 → ψ : MvPolynomial (Fin n ⊕ Fin n) ℝ with totalDegree ≤ 2s + 1, evaluated at (X, X′); reason: same polynomials
--   - encoding: E_{X,ξ_i,ξ_j,X′} → the integral over (X, ξ) ⊗ X′; reason: the integrand depends only on X, ξ_i, ξ_j, X′
-- source:
--   Zhou, Linear Regression with Self-Selection Bias in Polynomial Time, STOC 2027 submission (manuscript sha256 5d65f750…), Lemma 8.8, (118), p.62 (PDF p.65); proof Appendix F.3

import Mathlib
import Definitions.Def_SelfSelReg_jointLaw
import Definitions.Def_SelfSelReg_SatisfiesAssumption
import Definitions.Def_SelfSelReg_hypK
import Definitions.Def_SelfSelReg_restrictedMoment

open MeasureTheory ProbabilityTheory

namespace SelfSelReg

/-- **Lemma 8.8** (Pairwise Exceedance Bound).

F. Zhou, *Linear Regression with Self-Selection Bias in Polynomial Time*, STOC 2027 submission
(manuscript sha256 5d65f750…), Lemma 8.8, p.62 (PDF p.65): "Consider the Gaussian self-selection model
(Definition 1.1) under the boundedness and uncoveredness assumptions (Assumption 1.2). Use the choice
of K from Hyperparameters 4.1. Let s ≥ 1 be an integer and suppose T > 0 and T² ≥ Ks. Let
X ∼ N(0, I_n) be the covariate and let ξ_1, …, ξ_k ∼ N(0, 1) be independent noises, independent of X.
Let X′ ∼ N(0, I_n) be independent of the covariate and noises. Fix a real polynomial ψ(X, X′) of
degree at most 2s + 1. For every pair of distinct indices i, j ∈ [k] and every 1 ≤ r ≤ s,
E_{X,ξ_i,ξ_j,X′}[|ψ(X, X′)| 1{Y_i > T, Y_j > T}] ≤ e^{4s log K − T²/(2K)} ‖ψ‖_{L²(X,X′)} λ_j^{(2r)}." (118)

**Formalization Note.** `K = hypK B ∆`; `s`, `T` free, as on the page. `ψ` is a real polynomial in the
`2n` coordinates of `(X, X′)` (`MvPolynomial (Fin n ⊕ Fin n) ℝ`, `X` the left variables) of total
degree at most `2s + 1`. The expectation is over `(X, ξ) ∼ jointLaw` and an independent
`X′ ∼ N(0, I_n)` (the integrand depends on `ξ_i, ξ_j` only); `‖ψ‖_{L²(X,X′)} = (E ψ(X, X′)²)^{1/2}`.
A polynomial is integrable against these Gaussian laws. -/
theorem lemma_8_8 (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (hkn : k ≤ n) (B Δ : ℝ) (hB : 1 ≤ B)
    (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (w : Fin k → EuclideanSpace ℝ (Fin n))
    (hw : SatisfiesAssumption B Δ w) (s : ℕ) (hs : 1 ≤ s) (T : ℝ) (hT : 0 < T)
    (hTs : hypK B Δ * s ≤ T ^ 2) (ψ : MvPolynomial (Fin n ⊕ Fin n) ℝ)
    (hψ : ψ.totalDegree ≤ 2 * s + 1) (i j : Fin k) (hij : i ≠ j) (r : ℕ) (hr : 1 ≤ r)
    (hrs : r ≤ s) :
    ∫ p, |MvPolynomial.eval (Sum.elim (fun a => p.1.1 a) (fun a => p.2 a)) ψ| *
        Set.indicator {p : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin k)) ×
            EuclideanSpace ℝ (Fin n) |
          T < response w p.1.1 p.1.2 i ∧ T < response w p.1.1 p.1.2 j} 1 p
        ∂((jointLaw n k).prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) ≤
      Real.exp (4 * s * Real.log (hypK B Δ) - T ^ 2 / (2 * hypK B Δ)) *
        Real.sqrt (∫ q, MvPolynomial.eval (Sum.elim (fun a => q.1 a) (fun a => q.2 a)) ψ ^ 2
          ∂((stdGaussian (EuclideanSpace ℝ (Fin n))).prod
            (stdGaussian (EuclideanSpace ℝ (Fin n))))) *
        weight w T j r := by sorry

end SelfSelReg
