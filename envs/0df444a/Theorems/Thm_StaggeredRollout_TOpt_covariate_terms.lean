-- Prove2me | Theorems.Thm_StaggeredRollout_TOpt_covariate_terms
-- name    : StaggeredRollout.TOpt.covariate_terms
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T04:00:18.385828+00:00
-- url     : https://prove2.me/theorems/628cfc6b-9d99-4d79-9b42-3168885ceaed
-- title:
--   Proof of Theorem 3.1, p. ec25 (corrected: f_{j,X} as in corrected Lemma EC.1.2) — f_{j,X}, f_{j,U} ≥ 0, with value 0 when X⊤z_t, U⊤z_t are constant in t
-- statement:
--   **The covariate terms** (proof of Theorem 3.1, p. ec25).
--
--   Let $z\in\mathbb R^{N\times T}$ be any array, $X\in\mathbb R^{N\times d_x}$, $U\in\mathbb R^{N\times d_u}$, $\ell\ge0$, and let $f_{j,X}$, $f_{j,U}$ be the covariate terms of the (corrected) Lemma EC.1.2,
--   $$
--   f_{j,X}(z)=\tfrac1N\,z_{j:j_\ell}^\top\big(P_{1_{T_\ell}}\otimes H_X\big)z_{j:j_\ell},\qquad
--   f_{j,U}(z)=\tfrac1N\,z_{j:j_\ell}^\top\big(P_{1_{T_\ell}}\otimes U(I_{d_u}+U^\top U)^{-1}U^\top\big)z_{j:j_\ell}.
--   $$
--   Then for every window $j$:
--
--   1. $f_{j,X}(z)\ge0$ and $f_{j,U}(z)\ge0$;
--   2. if $X^\top z_t$ is the same vector $\mu_X$ for all $t$, then $f_{j,X}(z)=0$;
--   3. if $U^\top z_t$ is the same vector $\mu_U$ for all $t$, then $f_{j,U}(z)=0$.
--
--   So the minimum value $0$ of each covariate term is attained by every design whose cohorts balance the covariates, which is where the sets $\mathbb A_X$ and $\mathbb A_U$ of Theorem 3.1 come from.
--
--   **Formalization Note** The statement is for real arrays $z$ and arbitrary $X$, $U$; windows are 0-based.
--
--   Differences from the source:
--   - correction: f_{j,X}(Z) = Σ_k (ω^{x_k}_{j:j_ℓ})⊤ P_{1_{T_ℓ}} ω^{x_k}_{j:j_ℓ} → f_{j,X} = (1/N) z⊤(P_{1_{T_ℓ}} ⊗ H_X) z (fXj), as in the corrected Lemma EC.1.2; reason: the printed form is not the X-term of tr Prec(τ̂) unless X⊤X = N·I (counterexample in Lemma EC.1.2: N = 4, T = 2, ℓ = 0, X = (2, −2, 1, −1)⊤, A = (1, 2, ∞, 2)); the page's claims (≥ 0, zero when X⊤z_t is constant) hold for the corrected term
--   - reading: '(·) ≥ 0 for all z and the minimum value is attained when X⊤z_t is the same for all t' → 0 ≤ fXj, and (∃ μX, ∀ t, X⊤z_t = μX) → fXj = 0 (and the same for U); reason: the minimum value of a nonnegative term attained under the condition is 0
--   - generalization: z ∈ {−1, +1}^{N×T} from a staggered design, X and U centred and orthogonal (hypotheses of Theorem 3.1) → any real array z, any X and U; reason: the claims hold without these conditions and specialize to the page's
--   - encoding: periods 1, …, T and adoption time ∞ → Fin T (0-based: period t is index t − 1) and ⊤ of WithTop (Fin T); reason: Lean convention; same instances, and ⊤ keeps 'larger = later' (footnote 6)
-- source:
--   Xiong, Athey, Bayati, Imbens, Optimal Experimental Design for Staggered Rollouts, arXiv:1911.03764v6, p. ec25 (PDF 61), proof of Theorem 3.1, the two paragraphs after Case 3

import Mathlib
import Definitions.Def_StaggeredRollout_TOpt_Quadratic

namespace StaggeredRollout.TOpt
open Matrix

theorem covariate_terms (N T ℓ dx du : ℕ)
    (X : Matrix (Fin N) (Fin dx) ℝ) (U : Matrix (Fin N) (Fin du) ℝ)
    (z : Fin N → Fin T → ℝ) :
    (∀ j, 0 ≤ fXj ℓ X z j) ∧ (∀ j, 0 ≤ fUj ℓ U z j) ∧
    ((∃ μX : Fin dx → ℝ, ∀ t, Xᵀ *ᵥ (fun i => z i t) = μX) → ∀ j, fXj ℓ X z j = 0) ∧
    ((∃ μU : Fin du → ℝ, ∀ t, Uᵀ *ᵥ (fun i => z i t) = μU) → ∀ j, fUj ℓ U z j = 0) := by sorry

end StaggeredRollout.TOpt
