-- Prove2me | Theorems.Thm_PatakiRank_Mult_theorem_2_1_part_2
-- name    : PatakiRank.Mult.theorem_2_1_part_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:26:30.444006+00:00
-- url     : https://prove2.me/theorems/a3446d6d-b8b4-41fe-901b-94f20651a4d5
-- title:
--   Theorem 2.1, part 2, p. 342 — (y, Z) in a face G of the feasible set of (1.2): t(rank Z) ≤ t(n) − m + dim G
-- statement:
--   Let $C,A_1,\dots,A_m$ be symmetric $n\times n$ matrices and let $\mathcal G=\{(y,Z)\in\mathbb R^m\times\mathcal S^n:\ Z\succeq0,\ \sum_{i=1}^m y_iA_i+Z=C\}$ be the feasible set of the dual semidefinite program (1.2). Let $G$ be a face of $\mathcal G$, let $(y,Z)\in G$, and write $d=\dim G$, $s=\operatorname{rank}Z$. Then
--   $$t(s)\le t(n)-m+d.$$
--
--   This is the dual counterpart of part 1: at an extreme point of the dual feasible set the slack matrix has $t(\operatorname{rank}Z)\le t(n)-m$.
--
--   **Formalization Note** The pair is ordered $(y,Z)$ as on the page; the published predicate `IsDualFeasible C A Z y` takes the slack first. The bound is compared in $\mathbb Z$ (the right side may be negative a priori). As printed, the statement does not assume the $A_i$ linearly independent (the proof on p. 343 invokes it to parametrize the face by $Z$); the statement holds without it, because dependent $A_i$ add the dimension of $\{y:\sum y_iA_i=0\}$ to $\dim G$.
-- source:
--   Pataki, On the rank of extreme matrices in semidefinite programs and the multiplicity of optimal eigenvalues, Math. Oper. Res. 23(2) (1998), p. 342, Theorem 2.1, part 2 (2.2)

import Mathlib
import Definitions.Def_BurerMonteiro_RankIncrease_SDP
import Definitions.Def_ProjLikeRetr_Spectral_SpectralSet
import Definitions.Def_PatakiRank_Mult_Setting
open Matrix BurerMonteiro.RankIncrease ProjLikeRetr.Spectral

namespace PatakiRank.Mult

/-- Theorem 2.1, part 2 (p. 342): if `(y, Z) ∈ G` for a face `G` of the feasible set of (1.2),
then `t(rank Z) ≤ t(n) − m + dim G`. -/
theorem theorem_2_1_part_2 {n m : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.IsSymm)
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i, (A i).IsSymm)
    (G : Set ((Fin m → ℝ) × Matrix (Fin n) (Fin n) ℝ))
    (hG : IsFace {yZ | IsDualFeasible C A yZ.2 yZ.1} G)
    (y : Fin m → ℝ) (Z : Matrix (Fin n) (Fin n) ℝ) (hyZ : (y, Z) ∈ G) :
    ((tri Z.rank : ℕ) : ℤ) ≤ (tri n : ℤ) - m + convDim G := by sorry

end PatakiRank.Mult
