-- Prove2me | Theorems.Thm_SelfSelReg_corollary_5_3
-- name    : SelfSelReg.corollary_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:48:23.617665+00:00
-- url     : https://prove2.me/theorems/6ec8d55e-8069-4865-90e4-f349a4edfc99
-- title:
--   Corollary 5.3 — single-response Hermite identity $\mathbb E[H_d(X)\mathbf 1\{T\le Y_i\le T+1\}]=a_d(\sigma_i^2)w_i^{\otimes d}$
-- statement:
--   In the Gaussian self-selection model with regressors $w_1,\dots,w_k\in\mathbb R^n$ ($n\ge1$, $2\le k\le n$), let $\sigma_i^2=1+\|w_i\|_2^2$ and let $a_d(\sigma^2)=\int_T^{T+1}\phi_{\sigma^2}(t)\mathrm{He}_d(t/\sigma)/(\sigma^d\sqrt{d!})\,dt$ be the restricted moment coefficient at threshold $T$. Then for every $i\in[k]$ and every integer $d\ge0$,
--   $$\mathbb E_{X,\xi_i}\big[H_d(X)\,\mathbf 1\{T\le Y_i\le T+1\}\big]=a_d(\sigma_i^2)\,w_i^{\otimes d}.$$
--
--   Each single response therefore contributes an exact rank-one term to the restricted moments; the moment structure theorem bounds the error from responses that enter the slice without attaining the maximum.
--
--   **Formalization Note** The identity is stated entrywise and for every real threshold $T$.
--
--   Differences from the source:
--   - generalization: T is the hyperparameter T = 2K²√s of Hyperparameters 4.1 ("Throughout this work, we fix") → every real T; reason: the identity holds for every threshold and specializes to the hyperparameter
--   - encoding: E_{X,ξ_i}[·] → the integral over (X, ξ) under the model law; reason: the integrand depends only on X and ξ_i
--   - encoding: an identity of order-d tensors → an identity of every entry, indexed by J : Fin d → Fin n; reason: tensors are functions of index tuples; same content
-- source:
--   Zhou, Linear Regression with Self-Selection Bias in Polynomial Time, STOC 2027 submission (manuscript sha256 5d65f750…), Corollary 5.3, (28), p.20 (PDF p.23)

import Mathlib
import Definitions.Def_GaussPart_hermiteTensor
import Definitions.Def_SelfSelReg_jointLaw
import Definitions.Def_SelfSelReg_Tensor
import Definitions.Def_SelfSelReg_restrictedMoment

open MeasureTheory ProbabilityTheory

namespace SelfSelReg

/-- **Corollary 5.3** (Single-Response Hermite Identity).

F. Zhou, *Linear Regression with Self-Selection Bias in Polynomial Time*, STOC 2027 submission
(manuscript sha256 5d65f750…), Corollary 5.3, p.20 (PDF p.23): "In the Gaussian self-selection model
(Definition 1.1), for every i ∈ [k] and integer d ≥ 0, E_{X,ξ_i}[H_d(X) 1{T ≤ Y_i ≤ T + 1}] =
a_d(σ_i²) w_i^{⊗d}." (28)

**Formalization Note.** Entrywise identity of order-`d` tensors; `a_d` is `coeff T d` (17) with the
same `T`, and `σ_i² = 1 + ‖w_i‖²`. The paper's `T` is the hyperparameter of Hyperparameters 4.1; the
statement is made for every real `T` (a generalization). The expectation is over `(X, ξ)`; the
integrand depends only on `X, ξ_i`. The integrand is a polynomial times an indicator, hence
integrable. -/
theorem corollary_5_3 (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (hkn : k ≤ n)
    (w : Fin k → EuclideanSpace ℝ (Fin n)) (T : ℝ) (i : Fin k) (d : ℕ) (J : Fin d → Fin n) :
    ∫ z, GaussPart.hermiteTensor d z.1 J *
        Set.indicator {z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin k) |
          T ≤ response w z.1 z.2 i ∧ response w z.1 z.2 i ≤ T + 1} 1 z ∂(jointLaw n k) =
      coeff T d (sigmaSq w i) * tensorPow (w i) d J := by sorry

end SelfSelReg
