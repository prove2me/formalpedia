-- Prove2me | Theorems.Thm_PatakiRank_Mult_theorem_2_2
-- name    : PatakiRank.Mult.theorem_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:26:24.307736+00:00
-- url     : https://prove2.me/theorems/cb4ef6e5-e025-4997-b902-544b2da13364
-- title:
--   Theorem 2.2, p. 343 — multi-block SDP: Σ_j t(rank X_j) ≤ m − q + dim G on a face G
-- statement:
--   Consider a semidefinite program whose feasible set consists of the tuples $(X_1,\dots,X_p,y)$ with $X_j\in\mathcal S^n$, $y\in\mathbb R^q$ and
--   $$X_1\succeq0,\dots,X_p\succeq0,\qquad \sum_{j=1}^pA_{ij}\bullet X_j=b_i\ (i=1,\dots,m_1),\qquad \sum_{j=1}^pa_{ij}X_j+\sum_{j=1}^qy_jD_{ij}=B_i\ (i=1,\dots,m_2),$$
--   where $A_{ij},D_{ij},B_i$ are symmetric $n\times n$ matrices and $a_{ij},b_i$ are scalars. Let $m=m_1+m_2\,t(n)$ be the total number of equality constraints, a matrix equation in $\mathcal S^n$ counting as $t(n)$ scalar ones. If $(X_1,\dots,X_p,y)\in G$, where $G$ is a face of the feasible set, $d=\dim G$ and $r_j=\operatorname{rank}X_j$, then
--   $$\sum_{j=1}^p t(r_j)\le m-q+d.$$
--
--   This is the form of the rank bound used for the SDP reformulation (4.26) of the eigenvalue problem, which has two matrix blocks $V,W$ and $m+1$ free variables $(x,z)$.
--
--   **Formalization Note** The paper lets the matrix $B_i$ have its own order $n_i$ and $m=m_1+\sum_i t(n_i)$; here all matrices have one common order $n$, so $m=m_1+m_2t(n)$. This is the case the proof is written for and the case used in Theorem 4.3. The bound is compared in $\mathbb Z$.
-- source:
--   Pataki, On the rank of extreme matrices in semidefinite programs and the multiplicity of optimal eigenvalues, Math. Oper. Res. 23(2) (1998), p. 343, Theorem 2.2 (2.7)

import Mathlib
import Definitions.Def_BurerMonteiro_RankIncrease_SDP
import Definitions.Def_ProjLikeRetr_Spectral_SpectralSet
import Definitions.Def_PatakiRank_Mult_Setting
open Matrix BurerMonteiro.RankIncrease ProjLikeRetr.Spectral

namespace PatakiRank.Mult

/-- Theorem 2.2 (p. 343), with one common order `n` for all matrices, so that
`m = m₁ + m₂ · t(n)`: if `(X₁, …, X_p, y) ∈ G` for a face `G` of the feasible set, then
`∑_j t(rank X_j) ≤ m − q + dim G`. -/
theorem theorem_2_2 {n p q m₁ m₂ : ℕ} (Ablk : Fin m₁ → Fin p → Matrix (Fin n) (Fin n) ℝ)
    (b : Fin m₁ → ℝ) (a : Fin m₂ → Fin p → ℝ) (D : Fin m₂ → Fin q → Matrix (Fin n) (Fin n) ℝ)
    (Bm : Fin m₂ → Matrix (Fin n) (Fin n) ℝ) (hAblk : ∀ i j, (Ablk i j).IsSymm)
    (hD : ∀ i j, (D i j).IsSymm) (hBm : ∀ i, (Bm i).IsSymm)
    (G : Set ((Fin p → Matrix (Fin n) (Fin n) ℝ) × (Fin q → ℝ)))
    (hG : IsFace (multiFeas Ablk b a D Bm) G)
    (X : Fin p → Matrix (Fin n) (Fin n) ℝ) (y : Fin q → ℝ) (hXy : (X, y) ∈ G) :
    ∑ j, ((tri (X j).rank : ℕ) : ℤ) ≤ ((m₁ + m₂ * tri n : ℕ) : ℤ) - q + convDim G := by sorry

end PatakiRank.Mult
