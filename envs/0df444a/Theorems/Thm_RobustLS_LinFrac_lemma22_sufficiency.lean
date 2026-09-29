-- Prove2me | Theorems.Thm_RobustLS_LinFrac_lemma22_sufficiency
-- name    : RobustLS.LinFrac.lemma22_sufficiency
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:38:02.002057+00:00
-- url     : https://prove2.me/theorems/c997f977-8931-479b-bc40-50f41b110ef4
-- title:
--   Lemma 2.2 (if) — full-block S-procedure: ‖T₄‖ < 1 and (10) ⪰ 0 imply det(I − T₄Δ) ≠ 0 and T(Δ) ⪰ 0
-- statement:
--   Let $T_1 = T_1^T \in \mathbb R^{d\times d}$, $T_2 \in \mathbb R^{d\times k}$, $T_3 \in \mathbb R^{l\times d}$ and $T_4 \in \mathbb R^{l\times k}$, and for $\Delta \in \mathbb R^{k\times l}$ let
--
--   $$
--   T(\Delta) = T_1 + T_2\Delta(I - T_4\Delta)^{-1}T_3 + T_3^T(I - T_4\Delta)^{-T}\Delta^TT_2^T .
--   $$
--
--   Suppose $\|T_4\| < 1$ (largest singular value) and there is a scalar $\tau \ge 0$ with
--
--   $$
--   \begin{bmatrix} T_1 - \tau T_2T_2^T & T_3^T - \tau T_2T_4^T \\ T_3 - \tau T_4T_2^T & \tau(I - T_4T_4^T) \end{bmatrix} \succeq 0 . \qquad (10)
--   $$
--
--   Then for every $\Delta \in \mathbb R^{k\times l}$ with $\|\Delta\| \le 1$, the matrix $I - T_4\Delta$ is invertible and $T(\Delta) \succeq 0$.
--
--   This is the "if" half of Lemma 2.2, the unstructured (full-block) S-procedure: it replaces a matrix inequality that must hold for a whole ball of rational perturbations by a single linear matrix inequality in one scalar.
--
--   **Formalization Note** $\|\cdot\|$ is the operator norm between Euclidean spaces; $\Delta$ may be rectangular, as the lemma's "appropriate size" allows.
-- source:
--   El Ghaoui & Lebret, Robust Solutions to Least-Squares Problems with Uncertain Data, SIAM J. Matrix Anal. Appl. 18(4):1035–1064 (1997), p. 1038, §2.2, Lemma 2.2 ("if" direction), Eqs. (9)–(10)

import Mathlib
import Definitions.Def_RobustLS_LinFrac_Core

open Matrix

namespace RobustLS.LinFrac

/-- El Ghaoui & Lebret, Robust Solutions to Least-Squares Problems with Uncertain Data,
SIAM J. Matrix Anal. Appl. 18(4) (1997), §2.2, Lemma 2.2, "if" direction, p. 1038 (PDF p. 4).
Let `T₁ = T₁ᵀ ∈ ℝ^{d×d}`, `T₂ ∈ ℝ^{d×k}`, `T₃ ∈ ℝ^{l×d}`, `T₄ ∈ ℝ^{l×k}`. If `‖T₄‖ < 1` and
there is `τ ≥ 0` with the block matrix (10) positive semidefinite, then for every
`Δ ∈ ℝ^{k×l}` with `‖Δ‖ ≤ 1` (largest singular value) we have `det(I − T₄Δ) ≠ 0` and
`T(Δ) ⪰ 0` (Eq. (9)). -/
theorem lemma22_sufficiency {d k l : ℕ} (T₁ : Matrix (Fin d) (Fin d) ℝ) (hT₁ : T₁ = T₁ᵀ)
    (T₂ : Matrix (Fin d) (Fin k) ℝ) (T₃ : Matrix (Fin l) (Fin d) ℝ)
    (T₄ : Matrix (Fin l) (Fin k) ℝ) (hT₄ : specNorm T₄ < 1) (τ : ℝ) (hτ : 0 ≤ τ)
    (h10 : (lemma22Block T₁ T₂ T₃ T₄ τ).PosSemidef) :
    ∀ Δ : Matrix (Fin k) (Fin l) ℝ, specNorm Δ ≤ 1 →
      (1 - T₄ * Δ).det ≠ 0 ∧ (lftT T₁ T₂ T₃ T₄ Δ).PosSemidef := by sorry

end RobustLS.LinFrac
