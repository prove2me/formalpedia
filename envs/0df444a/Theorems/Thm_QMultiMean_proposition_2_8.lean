-- Prove2me | Theorems.Thm_QMultiMean_proposition_2_8
-- name    : QMultiMean.proposition_2_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:08:12.057972+00:00
-- url     : https://prove2.me/theorems/da474cbe-6a9e-4f97-afbc-4fd78f4cbb7c
-- title:
--   Proposition 2.8 — classical sub-Gaussian estimator [LM19a] with $O(n)$ samples (corrected: $O(\max\{1,n\})$)
-- statement:
--   There is a universal constant $C$ such that the following holds. Let $\delta\in(0,1)$ and $n\ge\log(1/\delta)$. There are $K\le C\max\{1,n\}$ and a map $f:(\mathbb R^d)^K\to\mathbb R^d$ such that for every finite random variable $X$ over $\mathbb R^d$ with mean $\mu$ and covariance matrix $\Sigma$, the estimate $\tilde\mu=f(X_1,\dots,X_K)$ computed from $K$ independent samples of $X$ satisfies
--   $$\|\tilde\mu-\mu\|_2\le\sqrt{\frac{\mathrm{Tr}(\Sigma)}n}+\sqrt{\frac{\|\Sigma\|\log(1/\delta)}n}$$
--   with probability at least $1-\delta$.
--
--   This is the Lugosi–Mendelson sub-Gaussian estimator. It gives the $n\le d$ regime of Theorem 3.5 and the centring step of Algorithm 2.
--
--   Differences from the source:
--   - reading: the sub-Gaussian estimators output a mean estimate by using O(n) random experiments → K i.i.d. samples followed by a deterministic map f, with K and f chosen from d, δ, n before the random variable; reason: an estimator is a procedure applied to the samples of an unknown X
--   - correction: O(n) random experiments → K ≤ C·max(1, n) with a universal C chosen first; reason: the literal bound tends to 0 (as n → 0, since n ≥ log(1/δ) may be arbitrarily small) and then allows 0 queries; counterexample: with K = 0 samples f is a constant, and X ≡ c with c ≠ f() has error target 0 (Tr Σ = ‖Σ‖ = 0) and success probability 0
--   - encoding: a finite sample set Ω with 0 ∈ Ω → Ω = Fin (N+1) with distinguished point 0; reason: every finite pointed set is in bijection with some Fin (N+1); the estimator may depend on Ω anyway
--   - reading: log (base not stated) → natural logarithm Real.log; reason: the natural log gives the weaker hypothesis n ≥ log(d/δ) and the smaller error bound, so it is the stronger reading; a base change is absorbed by the query constant
--   - encoding: Tr(Σ) and the spectral norm ‖Σ‖ of Σ = E[XXᵀ] − E[X]E[X]ᵀ → traceCov = Σ_ω P(ω)‖X(ω) − µ‖₂² and covNorm = sup over unit v of Σ_ω P(ω)⟨v, X(ω) − µ⟩²; reason: equal for a probability mass function (Σ is positive semidefinite)
-- source:
--   Cornelissen, Hamoudi, Jerbi, Near-Optimal Quantum Algorithms for Multivariate Mean Estimation, arXiv:2111.09787v2, p.8, Proposition 2.8

import Mathlib
import Definitions.Def_QMultiMean_FiniteRandomVariable

set_option autoImplicit false

namespace QMultiMean

/-- Proposition 2.8 (Classical sub-Gaussian estimators, [LM19a]) of Cornelissen, Hamoudi, Jerbi,
arXiv:2111.09787v2, p.8: let `X` be a `d`-dimensional random variable with mean `µ` and covariance
matrix `Σ`. Given `δ ∈ (0, 1)` and `n ≥ log(1/δ)`, the sub-Gaussian estimator outputs `µ̃` with
`‖µ̃ − µ‖₂ ≤ √(Tr(Σ)/n) + √(‖Σ‖ log(1/δ)/n)` with probability at least `1 − δ`, using `O(n)` random
experiments.

**Formalization Note.** The estimator is `K` random experiments (Definition 2.4: i.i.d. samples of
`X`) followed by a deterministic map `f`, both chosen from `d, δ, n` before the random variable.
`O(n)` is `C·max(1, n)` with a universal `C` chosen first; the `max(1, ·)` corrects the literal
bound, which allows `0` samples as `n → 0`. Natural log. -/
theorem proposition_2_8 :
    ∃ C : ℝ, ∀ (d : ℕ) (δ n : ℝ), 0 < δ → δ < 1 → Real.log (1 / δ) ≤ n →
      ∃ K : ℕ, (K : ℝ) ≤ C * max 1 n ∧
        ∃ f : (Fin K → Vec d) → Vec d,
          ∀ (N : ℕ) (P : Fin (N + 1) → ℝ) (X : Fin (N + 1) → Vec d), IsPMF P →
            1 - δ ≤ sampleProb P X K f
              {est | ‖est - mean P X‖ ≤
                Real.sqrt (traceCov P X / n) +
                  Real.sqrt (covNorm P X * Real.log (1 / δ) / n)} := by sorry

end QMultiMean
