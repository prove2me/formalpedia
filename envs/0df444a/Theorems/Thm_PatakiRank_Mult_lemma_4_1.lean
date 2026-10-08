-- Prove2me | Theorems.Thm_PatakiRank_Mult_lemma_4_1
-- name    : PatakiRank.Mult.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:26:48.989583+00:00
-- url     : https://prove2.me/theorems/456375e0-30c3-43cd-8f4e-e9c90fe7b3ab
-- title:
--   Lemma 4.1, pp. 348–349 — the optimal set Θ of affine (EV_k) contains no line
-- statement:
--   Under the standing assumptions of §4 ($A_0,\dots,A_m$ linearly independent and symmetric, $m\ge1$, $1\le k<n$), the set $\Theta$ of optimal solutions of $(EV_k)\ \min\{f_k(A(x)):x\in\mathbb R^m\}$ does not contain a line: if $x,y\in\mathbb R^m$ and $x+\lambda y\in\Theta$ for all $\lambda\in\mathbb R$, then $y=0$.
--
--   Since $\Theta$ is closed and convex, this guarantees that $\Theta$ has an extreme point whenever it is nonempty (Rockafellar, Corollary 18.5.3), so Theorem 4.3 is not vacuous.
--
--   **Formalization Note** $\Theta$ is the argmin set of $f_k\circ A$. The hypothesis $k\ge1$ comes from p. 340 ($k\in\{1,\dots,n\}$); for $k=0$ the statement fails since $f_0\equiv0$.
-- source:
--   Pataki, On the rank of extreme matrices in semidefinite programs and the multiplicity of optimal eigenvalues, Math. Oper. Res. 23(2) (1998), pp. 348–349, Lemma 4.1

import Mathlib
import Definitions.Def_BurerMonteiro_RankIncrease_SDP
import Definitions.Def_ProjLikeRetr_Spectral_SpectralSet
import Definitions.Def_PatakiRank_Mult_Setting
open Matrix BurerMonteiro.RankIncrease ProjLikeRetr.Spectral

namespace PatakiRank.Mult

/-- Lemma 4.1 (pp. 348–349): under the standing assumptions of §4, `Θ` contains no line:
if `x + t y ∈ Θ` for all `t ∈ ℝ`, then `y = 0`. -/
theorem lemma_4_1 {n m k : ℕ} (A0 : Matrix (Fin n) (Fin n) ℝ) (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hA0 : A0.IsSymm) (hA : ∀ i, (A i).IsSymm)
    (hind : LinearIndependent ℝ (Fin.cons A0 A : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ))
    (hm : 1 ≤ m) (hk : 1 ≤ k) (hkn : k < n)
    (x y : Fin m → ℝ) (hline : ∀ t : ℝ, x + t • y ∈ Theta k A0 A) : y = 0 := by sorry

end PatakiRank.Mult
