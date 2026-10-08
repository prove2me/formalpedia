-- Prove2me | Theorems.Thm_SpikedWishart_SoftEdge_theorem_1_1_a
-- name    : SpikedWishart.SoftEdge.theorem_1_1_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:39:33.772322+00:00
-- url     : https://prove2.me/theorems/5eca7c40-9809-4309-9720-c3882aec410a
-- title:
--   Theorem 1.1(a), p. 1650 — at ℓ₁ = ⋯ = ℓ_k = 1+γ⁻¹, (λ₁ − (1+γ⁻¹)²)·γM^{2/3}/(1+γ)^{4/3} ⇒ F_k
-- statement:
--   Let $\lambda_1$ be the largest eigenvalue of the sample covariance matrix $S=\frac1M\sum_{k=1}^M\vec y_k\vec y_k^{\,*}$ of $M$ i.i.d. complex Gaussian samples of $N$ variables with covariance $\Sigma=U\,\mathrm{diag}(\ell_1,\dots,\ell_N)\,U^*$. Fix integers $0\le k\le r$, a bound $\gamma_0\ge1$ and a margin $c>0$. Let $M=M_n$, $N=N_n\to\infty$ with $\gamma=\gamma_n=\sqrt{M_n/N_n}\in[1,\gamma_0]$ and $N_n\ge r$, and for each $n$ let $U_n$ be any unitary matrix and suppose
--
--   1. $\ell_{r+1}=\dots=\ell_N=1$ (35);
--   2. $\ell_1=\dots=\ell_k=1+\gamma^{-1}$ (36);
--   3. $c\le\ell_j\le1+\gamma^{-1}-c$ for $k<j\le r$.
--
--   Then for every real $x$,
--   $$
--   \mathbb P\left(\big(\lambda_1-(1+\gamma^{-1})^2\big)\cdot\frac{\gamma}{(1+\gamma)^{4/3}}M^{2/3}\le x\right)\longrightarrow F_k(x)\qquad(n\to\infty),
--   $$
--   where $F_k(x)=\det\big(1-A-\sum_{m=1}^ks^{(m)}\otimes t^{(m)}\big)_{L^2((x,\infty))}$; $F_0$ is the GUE Tracy–Widom distribution.
--
--   This is the critical case of the phase transition: spikes below $1+\gamma^{-1}$ leave the Tracy–Widom limit unchanged, while $k$ spikes exactly at $1+\gamma^{-1}$ change the limit law to $F_k$ on the same $M^{2/3}$ scale.
--
--   **Formalization Note** "$M/N=\gamma^2$ in a compact subset of $[1,\infty)$" is encoded by sequences with $\gamma_n\in[1,\gamma_0]$, and "$\ell_{k+1},\dots,\ell_r$ in a compact subset of $(0,1+\gamma^{-1})$", whose right end moves with $\gamma_n$, by the fixed margin $c$; convergence is stated pointwise in $x$ (uniformity on compact sets follows from monotonicity and continuity of $F_k$). $F_k$ is the Fredholm determinant (201), which the paper shows equals Definition 1.1. The model is mean-zero complex Gaussian samples with $\mathbb E\,\vec y\vec y^{\,*}=\Sigma$ and $S=\frac1M\sum\vec y_k\vec y_k^{\,*}$ (the paper's (59)); $U_n$ ranges over all unitary matrices. Indices are $0$-based in Lean.
-- source:
--   Baik, Ben Arous and Péché, Phase transition of the largest eigenvalue for nonnull complex sample covariance matrices, Ann. Probab. 33 (2005), p. 1650, Theorem 1.1(a), (35)–(37)

import Mathlib
import Definitions.Def_SpikedWishart_SoftEdge_Model
import Definitions.Def_SpikedWishart_SoftEdge_Airy
open Filter Topology MeasureTheory

namespace SpikedWishart.SoftEdge

theorem theorem_1_1_a (r k : ℕ) (hkr : k ≤ r) (γ₀ c : ℝ) (hγ₀ : 1 ≤ γ₀) (hc : 0 < c)
    (M N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (γ : ℕ → ℝ) (hγ_def : ∀ n, γ n = Real.sqrt ((M n : ℝ) / (N n : ℝ)))
    (hγ : ∀ n, 1 ≤ γ n ∧ γ n ≤ γ₀) (hr : ∀ n, r ≤ N n)
    (U : ∀ n, Matrix.unitaryGroup (Fin (N n)) ℂ) (ℓ : ∀ n, Fin (N n) → ℝ)
    (hℓ_one : ∀ n (j : Fin (N n)), r ≤ (j : ℕ) → ℓ n j = 1)
    (hℓ_crit : ∀ n (j : Fin (N n)), (j : ℕ) < k → ℓ n j = 1 + (γ n)⁻¹)
    (hℓ_sub : ∀ n (j : Fin (N n)), k ≤ (j : ℕ) → (j : ℕ) < r →
      c ≤ ℓ n j ∧ ℓ n j ≤ 1 + (γ n)⁻¹ - c)
    (x : ℝ) :
    Tendsto (fun n => (sampleLaw (M n) (N n)).real
        {G | (largestEig (M n) (U n) (ℓ n) G - (1 + (γ n)⁻¹) ^ 2) *
            (γ n / (1 + γ n) ^ (4 / 3 : ℝ)) * (M n : ℝ) ^ (2 / 3 : ℝ) ≤ x})
      atTop (𝓝 (F k x)) := by sorry

end SpikedWishart.SoftEdge
