-- Prove2me | Theorems.Thm_PatakiRank_Mult_eq_4_31
-- name    : PatakiRank.Mult.eq_4_31
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:26:38.489974+00:00
-- url     : https://prove2.me/theorems/a80f59d5-54df-4788-b42c-b3b9e86ec6b2
-- title:
--   (4.31), p. 349 — dim F* = 1 if λ_k(A(x*)) > λ_{k+1}(A(x*)), and 0 if λ_k = λ_{k+1}
-- statement:
--   Under the standing assumptions of §4 ($A_0,\dots,A_m$ linearly independent and symmetric, $m\ge1$, $1\le k<n$), let $x^*\in\mathbb R^m$, $F^*=\{x^*\}\times\Omega_k(A(x^*))$ and $\lambda_i=\lambda_i(A(x^*))$. Then
--   $$\dim F^*=\begin{cases}1&\text{if }\lambda_k>\lambda_{k+1},\\0&\text{if }\lambda_k=\lambda_{k+1}.\end{cases}$$
--
--   Combined with the face bound (4.32), the case $\dim F^*=1$ is ruled out when $m>k(n-k)$; this is how (4.29) is proved.
--
--   **Formalization Note** The page states (4.31) for the extreme point $x^*$ of Theorem 4.3, but extremality plays no role, so it is stated for every $x^*$. Since $\lambda_k\ge\lambda_{k+1}$ always, the two cases are written as `if λ_{k+1} < λ_k then 1 else 0`. Dimension is the integer-valued `convDim`.
-- source:
--   Pataki, On the rank of extreme matrices in semidefinite programs and the multiplicity of optimal eigenvalues, Math. Oper. Res. 23(2) (1998), p. 349, (4.31) in the proof of Theorem 4.3

import Mathlib
import Definitions.Def_BurerMonteiro_RankIncrease_SDP
import Definitions.Def_ProjLikeRetr_Spectral_SpectralSet
import Definitions.Def_PatakiRank_Mult_Setting
open Matrix BurerMonteiro.RankIncrease ProjLikeRetr.Spectral

namespace PatakiRank.Mult

/-- (4.31) (p. 349, proof of Theorem 4.3): under the standing assumptions of §4, for every
`x* ∈ ℝ^m`, `dim F* = 1` if `λ_k(A(x*)) > λ_{k+1}(A(x*))` and `dim F* = 0` if
`λ_k(A(x*)) = λ_{k+1}(A(x*))`. -/
theorem eq_4_31 {n m k : ℕ} (A0 : Matrix (Fin n) (Fin n) ℝ) (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hA0 : A0.IsSymm) (hA : ∀ i, (A i).IsSymm)
    (hind : LinearIndependent ℝ (Fin.cons A0 A : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ))
    (hm : 1 ≤ m) (hk : 1 ≤ k) (hkn : k < n)
    (xs : Fin m → ℝ) :
    convDim (Fstar k A0 A xs) =
      if eig (Aff A0 A xs) ⟨k, hkn⟩ < eig (Aff A0 A xs) ⟨k - 1, by omega⟩ then 1 else 0 := by sorry

end PatakiRank.Mult
