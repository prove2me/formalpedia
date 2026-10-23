-- Prove2me | Theorems.Thm_StaggeredRollout_TOpt_theorem_3_1
-- name    : StaggeredRollout.TOpt.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:59:38.496557+00:00
-- url     : https://prove2.me/theorems/ea0ff415-a94f-4696-b164-d0e6f490bcb4
-- title:
--   Theorem 3.1, p. 13 — every design in 𝔸_opt = 𝔸_ℓ ∩ 𝔸_X ∩ 𝔸_U maximizes tr Prec(τ̂) over all staggered designs
-- statement:
--   **Theorem 3.1 (Optimality Conditions).**
--
--   Consider $N$ units, $T$ periods and $\ell\ge0$ lags, a staggered design $A\in([T]\cup\{\infty\})^N$ with treatment path $z_{it}=+1$ if $A_i\le t$ and $-1$ otherwise, observed covariates $X\in\mathbb R^{N\times d_x}$ and latent covariates $U\in\mathbb R^{N\times d_u}$. The effects $\tau_0,\dots,\tau_\ell$ are estimated by the infeasible GLS with weight $\propto(U\Sigma_vU^\top+\sigma_\varepsilon^2I_N)^{-1}$, and $\operatorname{tr}\operatorname{Prec}(\hat\tau;A)$ is the trace of its precision under $A$. Suppose that
--
--   1. $\sigma_\varepsilon^2>0$ and $\Sigma_v=\sigma_\varepsilon^2I_{d_u}$;
--   2. the rows of $X$ and of $U$ are centred, $\sum_{i=1}^NX_i=0_{d_x}$ and $\sum_{i=1}^Nu_i=0_{d_u}$;
--   3. $X$ and $U$ are orthogonal, $\sum_{i=1}^NX_iu_i^\top=0_{d_x\times d_u}$;
--   4. if $\ell>0$, then $T>(\ell^3+13\ell^2+7\ell+3)/(8\ell)$.
--
--   If $A\in\mathbb A_{\mathrm{opt}}=\mathbb A_\ell\cap\mathbb A_X\cap\mathbb A_U$, then $A$ is a T-optimal design:
--   $$
--   \operatorname{tr}\operatorname{Prec}(\hat\tau;A')\le\operatorname{tr}\operatorname{Prec}(\hat\tau;A)\qquad\text{for every design }A'\in([T]\cup\{\infty\})^N.
--   $$
--   Here $\mathbb A_\ell$ fixes the treated fraction at each period to $(1+\omega^*_{\ell,t})/2$ with the S-shaped $\omega^*_\ell$ of (3.4), and $\mathbb A_X$, $\mathbb A_U$ require every adoption cohort after the first period to have covariate sum zero.
--
--   The theorem turns the integer program (3.2) into explicit conditions: an S-shaped rollout of the treated fraction plus covariate balance of the adoption cohorts.
--
--   **Formalization Note** The precision is the deterministic GLS precision of (EC.2.1)–(EC.2.2), encoded junk-free in the definitions file; the probability model enters only through the error covariance $I\otimes\Psi$. The comparison design $A'$ ranges over all of `Fin N → WithTop (Fin T)`. When $\mathbb A_{\mathrm{opt}}$ is empty the statement is vacuous, as the page's "if" allows; it is nonempty for instance at $\ell=0$, $T=2$, $N=4$, $A=(1,2,2,\infty)$ with $X=(1,-1,1,-1)^\top$, $U=(1,1,-1,-1)^\top$.
--
--   Differences from the source:
--   - encoding: Assumptions 2.1, 2.2, 3.1 and the random model (3.1) with infeasible GLS weight W ∝ (UΣ_vU⊤ + σ²_ε I_N)⁻¹ → a design A : Fin N → WithTop (Fin T) with z_it = ±1 by A_i ≤ t (irreversible adoption, known ℓ) and the precision computed with Σ_e = I ⊗ Ψ, Ψ = UΣ_vU⊤ + σ²_ε I_N; reason: these are the only ways the assumptions enter tr Prec(τ̂) ((EC.2.1), Remark 3.2); the Gauss–Markov/Aitken theorem (VectorSpaceOpt.gauss_markov) gives Var of GLS = (W⊤Σ⁻¹W)⁻¹, and the proportionality constant of W does not change the estimator
--   - generalization: Prec(τ̂; A) from (EC.2.2), with nuisance matrix Γ normalized by α_{N−p+1:N} = 0 → Σ_j min_γ of the Σ_e⁻¹-weighted residual sum of squares of the lag-j column on all N unit dummies and the per-period columns [1, X] (traceT); reason: same column span as Γ, so the same value whenever (EC.2.2) is defined; also defined (as the trace of the Fisher information of τ) when Γ⊤Σ_e⁻¹Γ is singular or the design makes Var(τ̂) singular
--   - reading: T > (ℓ³ + 13ℓ² + 7ℓ + 3)/(8ℓ) → 0 < ℓ → (ℓ³ + 13ℓ² + 7ℓ + 3)/(8ℓ) < T; reason: the expression is undefined at ℓ = 0, where Example 3.2 gives ω* for every T and the proof needs no condition
--   - encoding: periods 1, …, T and adoption time ∞ → Fin T (0-based: period t is index t − 1) and ⊤ of WithTop (Fin T); reason: Lean convention; same instances, and ⊤ keeps 'larger = later' (footnote 6)
--   - encoding: σ²_ε a variance, Ψ⁻¹ used as GLS weight → hypothesis 0 < σ²_ε; reason: excludes only the case where Ψ need not be invertible and the infeasible GLS weight is undefined
--   - encoding: Σ_v = σ²_ε · I_{d_u} → a matrix parameter Sv with hypothesis Sv = σ²_ε • 1; reason: same instances
--   - encoding: Σ_i X_i = 0_{d_x}, Σ_i u_i = 0_{d_u}, Σ_i X_i u_i⊤ = 0_{d_x×d_u} → ∀ k, Σ_i X i k = 0; ∀ k, Σ_i U i k = 0; Xᵀ * U = 0; reason: same conditions, coordinatewise
--   - encoding: N⁻¹ Σ_i 1{A_i ≤ t} and N⁻¹ Σ_i X_i 1{A_i = t} in 𝔸_ℓ, 𝔸_X, 𝔸_U → the same with Lean's (N : ℝ)⁻¹; reason: identical for N ≥ 1; at N = 0, where the page's N⁻¹ is undefined, 𝔸_ℓ is empty for T ≥ 1
-- source:
--   Xiong, Athey, Bayati, Imbens, Optimal Experimental Design for Staggered Rollouts, arXiv:1911.03764v6, p. 13, Theorem 3.1 and (3.5); objective (3.2) on p. 11; 𝔸_ℓ, 𝔸_X, 𝔸_U on p. 13

import Mathlib
import Definitions.Def_StaggeredRollout_TOpt_Setting

namespace StaggeredRollout.TOpt
open Matrix

theorem theorem_3_1 (N T ℓ dx du : ℕ) (sig2 : ℝ) (hsig : 0 < sig2)
    (X : Matrix (Fin N) (Fin dx) ℝ) (U : Matrix (Fin N) (Fin du) ℝ)
    (Sv : Matrix (Fin du) (Fin du) ℝ)
    (hXc : ∀ k, ∑ i, X i k = 0) (hUc : ∀ k, ∑ i, U i k = 0) (hXU : Xᵀ * U = 0)
    (hSv : Sv = sig2 • (1 : Matrix (Fin du) (Fin du) ℝ))
    (hT : 0 < ℓ → ((ℓ : ℝ) ^ 3 + 13 * (ℓ : ℝ) ^ 2 + 7 * (ℓ : ℝ) + 3) / (8 * (ℓ : ℝ)) < (T : ℝ))
    (A : Fin N → WithTop (Fin T)) (hA : A ∈ Aell ℓ ∩ AX X ∩ AU U) :
    ∀ A' : Fin N → WithTop (Fin T), traceT ℓ sig2 X U Sv A' ≤ traceT ℓ sig2 X U Sv A := by sorry

end StaggeredRollout.TOpt
