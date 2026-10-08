-- Prove2me | Theorems.Thm_PDASNewton_Local_GF_invertible_bounded
-- name    : PDASNewton.Local.GF_invertible_bounded
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:08:35.38434+00:00
-- url     : https://prove2.me/theorems/a8b6fb48-bcaf-4c1a-bc66-67d9469aee2b
-- title:
--   §2 (2.7)–(2.8), p. 5, and §3, p. 7 — for a P-matrix, every G_F(x) is nonsingular and the inverses are uniformly bounded
-- statement:
--   Let $A \in \mathbb{R}^{n \times n}$ be a P-matrix (all principal minors positive), $\psi \in \mathbb{R}^n$ and $c > 0$. For $x = (y, \lambda)$ let $G_F(x)$ be the system matrix of (2.4). Then there is a constant $M$ such that for every $x \in \mathbb{R}^n \times \mathbb{R}^n$ the linear map $G_F(x)$ has a two-sided inverse with
--   $$\|G_F(x)^{-1}\| \le M.$$
--
--   Solvability is the paper's argument through (2.7)–(2.8), which uses that the principal block $A_{\mathcal{I}}$ on the inactive set is regular for a P-matrix; the uniform bound is the boundedness requirement of Theorem 1.1 noted on p. 7.
--
--   **Formalization Note** Nonsingular means a two-sided continuous linear inverse; the bound is on the operator norm of the inverse for the product of sup norms. The P-matrix property is the published definition `RobinsonSR.Schur.IsPMatrix`.
-- source:
--   Hintermüller, Ito, Kunisch, The primal-dual active set strategy as a semismooth Newton method, HAL hal-01660511v1, p. 5, (2.7)–(2.8) and the sentence 'Since A is a P-matrix, A_𝓘k is regular'; p. 7, 'The boundedness requirement of (G_F)⁻¹ according to Theorem 1.1'

import Mathlib
import Definitions.Def_RobinsonSR_Schur_Setting
import Definitions.Def_PDASNewton_Local_Setting

namespace PDASNewton.Local

/-- §2, p. 5 (solvability of (2.4) via (2.7)–(2.8)) and §3, p. 7 (boundedness of `(G_F)⁻¹`):
for a P-matrix `A` and `c > 0`, every `G_F(x)` is nonsingular, and the inverses are bounded
uniformly in `x`. -/
theorem GF_invertible_bounded {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : RobinsonSR.Schur.IsPMatrix A) (ψ : Fin n → ℝ) (c : ℝ) (hc : 0 < c) :
    ∃ M : ℝ, ∀ x : (Fin n → ℝ) × (Fin n → ℝ),
      ∃ Ginv : ((Fin n → ℝ) × (Fin n → ℝ)) →L[ℝ] ((Fin n → ℝ) × (Fin n → ℝ)),
        Ginv.comp (GF A ψ c x) = ContinuousLinearMap.id ℝ _ ∧
        (GF A ψ c x).comp Ginv = ContinuousLinearMap.id ℝ _ ∧ ‖Ginv‖ ≤ M := by sorry

end PDASNewton.Local
