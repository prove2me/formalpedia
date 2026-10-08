-- Prove2me | Theorems.Thm_PatakiRank_Mult_theorem_4_3
-- name    : PatakiRank.Mult.theorem_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:26:57.788097+00:00
-- url     : https://prove2.me/theorems/b7e208b9-bdbc-4f96-962a-e1ee444d91f9
-- title:
--   Theorem 4.3, p. 349 — at an extreme point x* of Θ with m > k(n − k): λ_k(A(x*)) = λ_{k+1}(A(x*)) and mult(λ_k) ≥ n − τ(t(n) − m − 1, k − 1, n − k − 1)
-- statement:
--   Let $A_0,A_1,\dots,A_m$ be linearly independent symmetric $n\times n$ matrices with $m\ge1$, let $A(x)=A_0+\sum_{i=1}^mx_iA_i$, and let $1\le k<n$. Let $f_k(B)=\lambda_1(B)+\dots+\lambda_k(B)$ be the sum of the $k$ largest eigenvalues of a symmetric matrix $B$, and let $\Theta$ be the set of optimal solutions of the affine eigenvalue-optimization problem
--   $$(EV_k)\qquad \min\{f_k(A(x)):\ x\in\mathbb R^m\}.$$
--   Let $x^*$ be an extreme point of $\Theta$, and assume $m>k(n-k)$. Then
--   $$\lambda_k(A(x^*))=\lambda_{k+1}(A(x^*)) \tag{4.29}$$
--   and
--   $$\operatorname{mult}(\lambda_k(A(x^*)))\ \ge\ n-\tau\big(t(n)-m-1,\ k-1,\ n-k-1\big), \tag{4.30}$$
--   where $t(i)=i(i+1)/2$, $\tau(l,r,s)=\max\{i+j:\ t(i)+t(j)\le l,\ i\le r,\ j\le s\}$, and $\operatorname{mult}(\lambda_k)$ is the length of the maximal run of eigenvalues equal to $\lambda_k$.
--
--   This is the main result of the paper: when the number of free parameters exceeds $k(n-k)$, the $k$-th and $(k+1)$-st eigenvalues coalesce at extreme optimal solutions, so $f_k\circ A$ is nonsmooth there, and the multiplicity of the coalesced eigenvalue grows with $m$.
--
--   **Formalization Note** Eigenvalues are 0-based in Lean ($\lambda_k$ is `eig _ ⟨k-1,_⟩`, $\lambda_{k+1}$ is `eig _ ⟨k,_⟩`). Linear independence includes $A_0$, as on p. 348; it implies $m+1\le t(n)$, so the first argument of $\tau$ is nonnegative and the maximum is over a nonempty set. The bound (4.30) is compared in $\mathbb Z$. $\Theta$ is the argmin set and an extreme point is a one-point face, as defined in `PatakiRank.Mult.Setting`. The hypothesis $k\ge1$ is from p. 340, the others ($m\ge1$, $k<n$, independence, symmetry) are the standing assumptions of §4.
-- source:
--   Pataki, On the rank of extreme matrices in semidefinite programs and the multiplicity of optimal eigenvalues, Math. Oper. Res. 23(2) (1998), p. 349, Theorem 4.3 ((4.29), (4.30))

import Mathlib
import Definitions.Def_BurerMonteiro_RankIncrease_SDP
import Definitions.Def_ProjLikeRetr_Spectral_SpectralSet
import Definitions.Def_PatakiRank_Mult_Setting
open Matrix BurerMonteiro.RankIncrease ProjLikeRetr.Spectral

namespace PatakiRank.Mult

/-- Theorem 4.3 (p. 349): under the standing assumptions of §4, let `x*` be an extreme point of
`Θ` and assume `m > k(n − k)`. Then (4.29) `λ_k(A(x*)) = λ_{k+1}(A(x*))`, and (4.30)
`mult(λ_k(A(x*))) ≥ n − τ(t(n) − m − 1, k − 1, n − k − 1)`. -/
theorem theorem_4_3 {n m k : ℕ} (A0 : Matrix (Fin n) (Fin n) ℝ) (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hA0 : A0.IsSymm) (hA : ∀ i, (A i).IsSymm)
    (hind : LinearIndependent ℝ (Fin.cons A0 A : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ))
    (hm : 1 ≤ m) (hk : 1 ≤ k) (hkn : k < n)
    (xs : Fin m → ℝ) (hx : IsExtremePt (Theta k A0 A) xs) (hmk : k * (n - k) < m) :
    eig (Aff A0 A xs) ⟨k - 1, by omega⟩ = eig (Aff A0 A xs) ⟨k, hkn⟩ ∧
      (n : ℤ) - (tau ((tri n : ℤ) - m - 1) (k - 1) (n - k - 1) : ℤ) ≤
        (mult (Aff A0 A xs) ⟨k - 1, by omega⟩ : ℤ) := by sorry

end PatakiRank.Mult
