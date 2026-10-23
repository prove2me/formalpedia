-- Prove2me | Theorems.Thm_StaggeredRollout_TOpt_lemma_EC_1_2
-- name    : StaggeredRollout.TOpt.lemma_EC_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T04:00:35.016385+00:00
-- url     : https://prove2.me/theorems/975a06d3-4c8f-48ed-b691-42e5a1601001
-- title:
--   Lemma EC.1.2, p. ec12 (corrected: b_{ℓ,t} = (T_ℓ+1−2t)/T_ℓ; X-term weighted by the projector onto col X) — separable quadratic representation of tr Prec(τ̂)
-- statement:
--   **Separable quadratic representation** (Lemma EC.1.2, corrected).
--
--   Work in the setting of the definitions file: $N$ units, $T$ periods, $\ell$ lags, a staggered design $A$ with treatment path $z_{it}\in\{-1,+1\}$, observed covariates $X\in\mathbb R^{N\times d_x}$, latent covariates $U\in\mathbb R^{N\times d_u}$, and the infeasible GLS with per-period error covariance $\Psi=U\Sigma_vU^\top+\sigma_\varepsilon^2I_N$. Assume $\sigma_\varepsilon^2>0$, $\Sigma_v=\sigma_\varepsilon^2I_{d_u}$, the rows of $X$ and of $U$ are centred ($\sum_iX_i=0$, $\sum_iu_i=0$), and $\sum_iX_iu_i^\top=0$. Let $T_\ell=T-\ell$ and $\omega_t=\frac1N\sum_iz_{it}$. Then for every design $A$
--   $$
--   \operatorname{tr}\operatorname{Prec}(\hat\tau;A)=-\frac{N}{\sigma_\varepsilon^2}\sum_{j=1}^{\ell+1}\Big(\underbrace{\omega_{j:j_\ell}^\top P_{1_{T_\ell}}\omega_{j:j_\ell}+2b_\ell^\top\omega_{j:j_\ell}}_{f_{j,1}}+\underbrace{\tfrac1N z_{j:j_\ell}^\top(P_{1_{T_\ell}}\otimes H_X)z_{j:j_\ell}}_{f_{j,X}}+\underbrace{\tfrac1N z_{j:j_\ell}^\top M_U z_{j:j_\ell}}_{f_{j,U}}\Big),
--   $$
--   where $b_{\ell,t}=(T_\ell+1-2t)/T_\ell$, $H_X$ is the orthogonal projector onto the column space of $X$, and $M_U=P_{1_{T_\ell}}\otimes U(I_{d_u}+U^\top U)^{-1}U^\top$.
--
--   The representation splits the design objective into a term that depends only on the treated fractions $\omega_t$, a term that depends only on how treatment correlates with $X$, and one for $U$. A design that minimizes all three simultaneously maximizes $\operatorname{tr}\operatorname{Prec}(\hat\tau)$, which is how Theorem 3.1 is proved.
--
--   **Formalization Note** The identity is stated for every design $A$, with $z_{it}$, the windows and the three terms as in the definitions files (0-based windows `j : Fin (ℓ+1)`). If $T\le\ell$ there are no observed periods and both sides are $0$.
--
--   Differences from the source:
--   - correction: b_{ℓ,t} = (T_ℓ + 2 − 2t)/T_ℓ → b_{ℓ,t} = (T_ℓ + 1 − 2t)/T_ℓ (bl); reason: the printed value is false: d_x = d_u = 0, σ²_ε = 1, ℓ = 0, N = 2, T = 2, A = (1, 2) satisfies every hypothesis, the true trace is 1 and the printed formula gives −1; the corrected value is the one of the display closing the proof on p. ec20 and of Example 3.2
--   - correction: f_{j,X}(Z) = Σ_k (ω^{x_k}_{j:j_ℓ})⊤ P_{1_{T_ℓ}} ω^{x_k}_{j:j_ℓ} with ω^{x_k}_t = (1/N) Σ_i X_ik z_it → f_{j,X}(Z) = (1/N) z_{j:j_ℓ}⊤ (P_{1_{T_ℓ}} ⊗ H_X) z_{j:j_ℓ}, H_X the orthogonal projector onto col X (fXj); reason: the printed term is false unless X⊤X = N·I: ℓ = 0, d_u = 0, σ²_ε = 1, N = 4, T = 2, X = (2, −2, 1, −1)⊤ (centred), A = (1, 2, ∞, 2) gives true trace 0.2 and printed −2.5; the corrected term is the analogue of the printed U-term and reduces to the printed one when X⊤X = N·I
--   - encoding: H_X (no formula on the page) → (1/N) Σ_s (‖ẑ_s‖² − min_c ‖ẑ_s − Xc‖²) with ẑ_s the window-centred cross-section; reason: equals z⊤(P ⊗ H_X)z without a pseudo-inverse and without a rank condition on X
--   - encoding: M_U = P_{1_{T_ℓ}} ⊗ U(I + U⊤U)⁻¹U⊤ as a Kronecker product → the blockwise double sum Σ_{s,s'} (P_{1_{T_ℓ}})_{ss'} z_{j+s}⊤ U(I + U⊤U)⁻¹U⊤ z_{j+s'}; reason: the same quadratic form written block by block
--   - generalization: Prec(τ̂; A) from (EC.2.2), with nuisance matrix Γ normalized by α_{N−p+1:N} = 0 → Σ_j min_γ of the Σ_e⁻¹-weighted residual sum of squares of the lag-j column on all N unit dummies and the per-period columns [1, X] (traceT); reason: same column span as Γ, so the same value whenever (EC.2.2) is defined; also defined (as the trace of the Fisher information of τ) when Γ⊤Σ_e⁻¹Γ is singular or the design makes Var(τ̂) singular
--   - encoding: Assumptions 2.1, 2.2, 3.1 and the random model (3.1) with infeasible GLS weight W ∝ (UΣ_vU⊤ + σ²_ε I_N)⁻¹ → a design A : Fin N → WithTop (Fin T) with z_it = ±1 by A_i ≤ t (irreversible adoption, known ℓ) and the precision computed with Σ_e = I ⊗ Ψ, Ψ = UΣ_vU⊤ + σ²_ε I_N; reason: these are the only ways the assumptions enter tr Prec(τ̂) ((EC.2.1), Remark 3.2); the Gauss–Markov/Aitken theorem (VectorSpaceOpt.gauss_markov) gives Var of GLS = (W⊤Σ⁻¹W)⁻¹, and the proportionality constant of W does not change the estimator
--   - encoding: periods 1, …, T and adoption time ∞ → Fin T (0-based: period t is index t − 1) and ⊤ of WithTop (Fin T); reason: Lean convention; same instances, and ⊤ keeps 'larger = later' (footnote 6)
--   - encoding: σ²_ε a variance, Ψ⁻¹ used as GLS weight → hypothesis 0 < σ²_ε; reason: excludes only the case where Ψ need not be invertible and the infeasible GLS weight is undefined
--   - encoding: Σ_v = σ²_ε · I_{d_u} → a matrix parameter Sv with hypothesis Sv = σ²_ε • 1; reason: same instances
--   - encoding: Σ_i X_i = 0_{d_x}, Σ_i u_i = 0_{d_u}, Σ_i X_i u_i⊤ = 0_{d_x×d_u} → ∀ k, Σ_i X i k = 0; ∀ k, Σ_i U i k = 0; Xᵀ * U = 0; reason: same conditions, coordinatewise
--   - generalization: T_ℓ = T − ℓ ≥ 1 implicit → any T; for T ≤ ℓ both sides are empty sums equal to 0; reason: specializes to the page's claim for T > ℓ
-- source:
--   Xiong, Athey, Bayati, Imbens, Optimal Experimental Design for Staggered Rollouts, arXiv:1911.03764v6, p. ec12 (PDF 48), Lemma EC.1.2, (EC.1.7); corrected b_ℓ from p. ec20 (closing display of the proof) and Example 3.2

import Mathlib
import Definitions.Def_StaggeredRollout_TOpt_Setting
import Definitions.Def_StaggeredRollout_TOpt_Quadratic

namespace StaggeredRollout.TOpt
open Matrix

theorem lemma_EC_1_2 (N T ℓ dx du : ℕ) (sig2 : ℝ) (hsig : 0 < sig2)
    (X : Matrix (Fin N) (Fin dx) ℝ) (U : Matrix (Fin N) (Fin du) ℝ)
    (Sv : Matrix (Fin du) (Fin du) ℝ)
    (hXc : ∀ k, ∑ i, X i k = 0) (hUc : ∀ k, ∑ i, U i k = 0) (hXU : Xᵀ * U = 0)
    (hSv : Sv = sig2 • (1 : Matrix (Fin du) (Fin du) ℝ))
    (A : Fin N → WithTop (Fin T)) :
    traceT ℓ sig2 X U Sv A
      = -((N : ℝ) / sig2) * ∑ j : Fin (ℓ + 1),
          (f1j ℓ T (omegaBar (z A)) j + fXj ℓ X (z A) j + fUj ℓ U (z A) j) := by sorry

end StaggeredRollout.TOpt
