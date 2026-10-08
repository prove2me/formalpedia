-- Prove2me | Theorems.Thm_PatakiRank_Mult_theorem_2_1_part_1
-- name    : PatakiRank.Mult.theorem_2_1_part_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:26:21.20499+00:00
-- url     : https://prove2.me/theorems/e687e9b4-dfda-4b55-8c7a-9fe35727671a
-- title:
--   Theorem 2.1, part 1, p. 342 — X in a face F of the feasible set of (1.1): t(rank X) ≤ m + dim F
-- statement:
--   Let $A_1,\dots,A_m$ be symmetric $n\times n$ matrices and $b\in\mathbb R^m$, and let $\mathcal F=\{X\succeq0:\ A_i\bullet X=b_i,\ i=1,\dots,m\}$ be the feasible set of the semidefinite program (1.1). Let $F$ be a face of $\mathcal F$, let $X\in F$, and write $d=\dim F$, $r=\operatorname{rank}X$. Then
--   $$t(r)\le m+d,$$
--   where $t(r)=r(r+1)/2$.
--
--   For $d=0$ this is the bound on the rank of extreme matrices of an SDP: an extreme point of $\mathcal F$ has $t(\operatorname{rank}X)\le m$, so $\operatorname{rank}X=O(\sqrt m)$ regardless of $n$.
--
--   **Formalization Note** Faces and dimension are the paper's (see `PatakiRank.Mult.Setting`); the inequality is compared in $\mathbb Z$. As printed, no linear independence of the $A_i$ is assumed. The cost matrix $C$ of (1.1) does not affect the feasible set and is omitted.
-- source:
--   Pataki, On the rank of extreme matrices in semidefinite programs and the multiplicity of optimal eigenvalues, Math. Oper. Res. 23(2) (1998), p. 342, Theorem 2.1, part 1 (2.1)

import Mathlib
import Definitions.Def_BurerMonteiro_RankIncrease_SDP
import Definitions.Def_ProjLikeRetr_Spectral_SpectralSet
import Definitions.Def_PatakiRank_Mult_Setting
open Matrix BurerMonteiro.RankIncrease ProjLikeRetr.Spectral

namespace PatakiRank.Mult

/-- Theorem 2.1, part 1 (p. 342): if `X ∈ F` for a face `F` of the feasible set of (1.1), then
`t(rank X) ≤ m + dim F`. -/
theorem theorem_2_1_part_1 {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (A i).IsSymm) (b : Fin m → ℝ) (F : Set (Matrix (Fin n) (Fin n) ℝ))
    (hF : IsFace {X | IsPrimalFeasible A b X} F) (X : Matrix (Fin n) (Fin n) ℝ) (hX : X ∈ F) :
    ((tri X.rank : ℕ) : ℤ) ≤ (m : ℤ) + convDim F := by sorry

end PatakiRank.Mult
