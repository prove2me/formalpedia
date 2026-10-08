-- Prove2me | Theorems.Thm_SpikedWishart_Separated_theorem_1_1_b
-- name    : SpikedWishart.Separated.theorem_1_1_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:37:37.571511+00:00
-- url     : https://prove2.me/theorems/53ec8574-6b14-492c-8285-e6ef59de4d19
-- title:
--   Theorem 1.1(b), p. 1650 — for ℓ₁ = ⋯ = ℓ_k > 1+γ⁻¹, (λ₁ − ℓ₁ − ℓ₁γ⁻²/(ℓ₁−1))·√M/√(ℓ₁² − ℓ₁²γ⁻²/(ℓ₁−1)²) ⇒ G_k
-- statement:
--   Let $\lambda_1$ be the largest eigenvalue of the sample covariance matrix $S = \frac1M\sum_{k=1}^M\vec y_k\vec y_k^{\,*}$ of $M$ independent complex Gaussian samples $\vec y_k \in \mathbb C^N$ with mean zero and covariance $\Sigma$, and let $\ell_1,\dots,\ell_N$ be the eigenvalues of $\Sigma$. Fix an integer $r \ge 0$ and suppose $\ell_{r+1} = \cdots = \ell_N = 1$. Let $M, N \to \infty$ with $M/N = \gamma^2$ and $\gamma$ in a compact subset of $[1,\infty)$. Suppose that for some $1 \le k \le r$,
--   $$
--   \ell_1 = \cdots = \ell_k \ \text{ is in a compact subset of } (1+\gamma^{-1},\infty),
--   $$
--   and $\ell_{k+1},\dots,\ell_r$ are in a compact subset of $(0,\ell_1)$. Then for every real $x$,
--   $$
--   \mathbb P\left(\Big(\lambda_1 - \Big(\ell_1 + \frac{\ell_1\gamma^{-2}}{\ell_1 - 1}\Big)\Big)\cdot\frac{\sqrt M}{\sqrt{\ell_1^2 - \ell_1^2\gamma^{-2}/(\ell_1-1)^2}} \le x\right) \longrightarrow G_k(x),
--   $$
--   where $G_k$ is the distribution of the largest eigenvalue of the $k\times k$ GUE (28).
--
--   Above the threshold $1+\gamma^{-1}$, $\lambda_1$ separates from the bulk, its fluctuations are of order $M^{-1/2}$ instead of $M^{-2/3}$, and their law is that of the top eigenvalue of a $k\times k$ GUE, $k$ being the multiplicity of the largest population eigenvalue.
--
--   **Formalization Note** The regime is in sequence form: sequences $M_n, N_n$ with $N_n \to \infty$ and $\gamma_n = \sqrt{M_n/N_n} \in [1,\gamma_0]$; a sequence $L_n$ with $1 + \gamma_n^{-1} + c \le L_n \le C$ for the common value $\ell_1 = \cdots = \ell_k$ (the open end of the interval moves with $\gamma_n$, so "compact subset" is a fixed margin $c > 0$); $c \le \ell_j \le L_n - c$ for $k < j \le r$; $\ell_j = 1$ for $j > r$ (indices are 0-based in Lean). The covariance is $U_n\,\mathrm{diag}(\ell_n)\,U_n^*$ for an arbitrary unitary $U_n$. The convergence is stated for each fixed $x$; uniformity on compact sets of $x$ follows from monotonicity and continuity of $G_k$. The radicand is positive under these hypotheses, as the paper notes on p. 1678. The sample model is the one of the Model definition (mean-zero samples, factor $1/M$).
-- source:
--   Baik, Ben Arous and Péché, Phase transition of the largest eigenvalue for nonnull complex sample covariance matrices, Ann. Probab. 33 (2005), p. 1650, Theorem 1.1(b), (35), (38)–(39)

import Mathlib
import Definitions.Def_SpikedWishart_Separated_Model
import Definitions.Def_SpikedWishart_Separated_GUE

open Filter Topology MeasureTheory

namespace SpikedWishart.Separated

/-- Theorem 1.1(b), p. 1650. Sequence form of the regime: `M n, N n → ∞` with
`γ_n = √(M_n/N_n) ∈ [1, γ₀]`; population eigenvalues `ℓ_n` with `ℓ_1 = ⋯ = ℓ_k = L_n ∈
[1 + γ_n⁻¹ + c, C]`, `ℓ_{k+1}, …, ℓ_r ∈ [c, L_n − c]` and `ℓ_{r+1} = ⋯ = ℓ_N = 1`
(0-based indices `j`); covariance `U_n diag(ℓ_n) U_n*` with `U_n` unitary. -/
theorem theorem_1_1_b (r k : ℕ) (hk : 1 ≤ k) (hkr : k ≤ r) (γ₀ c C : ℝ) (hc : 0 < c)
    (M N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (hγ : ∀ n, 1 ≤ Real.sqrt ((M n : ℝ) / N n) ∧ Real.sqrt ((M n : ℝ) / N n) ≤ γ₀)
    (hr : ∀ n, r ≤ N n)
    (U : ∀ n, Matrix (Fin (N n)) (Fin (N n)) ℂ)
    (hU : ∀ n, U n ∈ Matrix.unitaryGroup (Fin (N n)) ℂ)
    (L : ℕ → ℝ) (hL : ∀ n, 1 + (Real.sqrt ((M n : ℝ) / N n))⁻¹ + c ≤ L n ∧ L n ≤ C)
    (ℓ : ∀ n, Fin (N n) → ℝ)
    (hspike : ∀ n (j : Fin (N n)), (j : ℕ) < k → ℓ n j = L n)
    (hmid : ∀ n (j : Fin (N n)), k ≤ (j : ℕ) → (j : ℕ) < r → c ≤ ℓ n j ∧ ℓ n j ≤ L n - c)
    (hnull : ∀ n (j : Fin (N n)), r ≤ (j : ℕ) → ℓ n j = 1)
    (x : ℝ) :
    Tendsto (fun n => (SpikedWishart.SoftEdge.sampleLaw (M n) (N n)).real
        {X | (largestEig (M n) (U n) (ℓ n) X -
              (L n + L n * (Real.sqrt ((M n : ℝ) / N n))⁻¹ ^ 2 / (L n - 1))) *
            Real.sqrt (M n) /
            Real.sqrt (L n ^ 2 - L n ^ 2 * (Real.sqrt ((M n : ℝ) / N n))⁻¹ ^ 2 / (L n - 1) ^ 2)
          ≤ x})
      atTop (𝓝 (G k x)) := by sorry

end SpikedWishart.Separated
