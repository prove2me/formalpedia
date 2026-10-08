-- Prove2me | Theorems.Thm_WassKF_Reform_inner_minimization_over_G
-- name    : WassKF.Reform.inner_minimization_over_G
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:09:06.182343+00:00
-- url     : https://prove2.me/theorems/682c7c48-46e7-4448-90f5-9f8abfd400e7
-- title:
--   Proof of Theorem 2.5, (A.6), p. 12 — $\min_G\langle D(G),S\rangle=\operatorname{Tr}[S_{xx}-S_{xy}S_{yy}^{-1}S_{yx}]$, uniquely at $G^\star=S_{xy}S_{yy}^{-1}$
-- statement:
--   Let $S \in \mathbb S^{n+m}_{++}$ be positive definite, partitioned as
--
--   $$
--   S = \begin{bmatrix} S_{xx} & S_{xy} \\ S_{yx} & S_{yy} \end{bmatrix}, \qquad S_{xx} \in \mathbb R^{n\times n},\ S_{yy} \in \mathbb R^{m \times m}.
--   $$
--
--   For $G \in \mathbb R^{n \times m}$ consider $\Bigl\langle \begin{bmatrix} I_n & -G \\ -G^\top & G^\top G \end{bmatrix}, S \Bigr\rangle$ with $\langle A, B\rangle = \operatorname{Tr}[A^\top B]$. Its least value over all $G \in \mathbb R^{n\times m}$ is attained and equals
--
--   $$
--   \min_{G} \Bigl\langle \begin{bmatrix} I_n & -G \\ -G^\top & G^\top G \end{bmatrix}, S \Bigr\rangle = \operatorname{Tr}\bigl[S_{xx} - S_{xy} S_{yy}^{-1} S_{yx}\bigr],
--   $$
--
--   the objective of program (5); and $G$ attains this value if and only if $G = G^\star = S_{xy} S_{yy}^{-1}$.
--
--   This is the step of the proof of Theorem 2.5 that turns the inner minimization over $G$ in (A.6) into the objective of (5).
--
--   **Formalization Note** The block matrix is `Matrix.fromBlocks 1 (-G) (-Gᵀ) (Gᵀ * G)`, the blocks of $S$ are `toBlocks₁₁`, `toBlocks₁₂`, `toBlocks₂₁`, `toBlocks₂₂`, and the right side is the published `sdpObjective S`. Since $S \succ 0$, $S_{yy}$ is invertible, so the matrix inverse has no junk value here.
-- source:
--   Shafieezadeh-Abadeh, Nguyen, Kuhn, Mohajerin Esfahani, Wasserstein Distributionally Robust Kalman Filtering, arXiv:1809.08830v3, p. 12, App. A.2, proof of Theorem 2.5, (A.6) and the first-order condition 2G⋆S_yy − 2S_xy = 0

import Mathlib
import Definitions.Def_WassersteinDRO_Shrinkage_sdpObjective

open Matrix

namespace WassKF.Reform

/-- Proof of Theorem 2.5, the minimization over `G` in (A.6), Shafieezadeh-Abadeh et al.,
arXiv:1809.08830v3, p. 12. For `S ≻ 0` partitioned as `[[S_xx, S_xy], [S_yx, S_yy]]`, the
function `G ↦ ⟨[[I_n, −G], [−Gᵀ, GᵀG]], S⟩` over `G ∈ ℝ^{n×m}` has least value
`Tr[S_xx − S_xy S_yy⁻¹ S_yx]` (the objective of (5)), and `G⋆ = S_xy S_yy⁻¹` is its unique
minimizer. The trace inner product is `⟨A, B⟩ = Tr[Aᵀ B]`. -/
theorem inner_minimization_over_G {n m : ℕ}
    (S : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) (hS : S.PosDef) :
    IsLeast (Set.range fun G : Matrix (Fin n) (Fin m) ℝ =>
        ((Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) ℝ) (-G) (-Gᵀ) (Gᵀ * G))ᵀ * S).trace)
      (WassersteinDRO.Shrinkage.sdpObjective S) ∧
    ∀ G : Matrix (Fin n) (Fin m) ℝ,
      ((Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) ℝ) (-G) (-Gᵀ) (Gᵀ * G))ᵀ * S).trace =
          WassersteinDRO.Shrinkage.sdpObjective S ↔
        G = S.toBlocks₁₂ * S.toBlocks₂₂⁻¹ := by sorry

end WassKF.Reform
