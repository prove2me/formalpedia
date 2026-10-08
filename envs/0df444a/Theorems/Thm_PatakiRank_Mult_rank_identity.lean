-- Prove2me | Theorems.Thm_PatakiRank_Mult_rank_identity
-- name    : PatakiRank.Mult.rank_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:26:50.981927+00:00
-- url     : https://prove2.me/theorems/3434a9a5-f801-4e65-b54f-e6b959f25b03
-- title:
--   §3, p. 348 — rank V + rank W + mult(λ_k(B)) = n for (z, V, W) ∈ Ω_k(B), z = ½(λ_k + λ_{k+1}), when λ_k(B) = λ_{k+1}(B)
-- statement:
--   Let $B$ be an $n\times n$ symmetric matrix, $1\le k<n$, and suppose $\lambda_k(B)=\lambda_{k+1}(B)$. Let $(z,V,W)\in\Omega_k(B)$ be an optimal solution of the SDP (3.14) with $z=\tfrac12(\lambda_k(B)+\lambda_{k+1}(B))$. Then
--   $$\operatorname{rank}V+\operatorname{rank}W+\operatorname{mult}(\lambda_k(B))=n.$$
--
--   This identity converts the upper bounds on the ranks of the slack matrices $V,W$ provided by the face bound of Theorem 2.2 into a lower bound on the multiplicity of $\lambda_k$; it is the step that turns (4.32) into (4.30) in the proof of Theorem 4.3.
--
--   **Formalization Note** The page states the identity without the hypothesis $\lambda_k(B)=\lambda_{k+1}(B)$. As printed it is false when $\lambda_k(B)>\lambda_{k+1}(B)$: for $n=2$, $k=1$, $B=\operatorname{diag}(2,0)$ one gets $z=1$, $V=\operatorname{diag}(1,0)$, $W=\operatorname{diag}(0,1)$ and $1+1+1=3\ne2$. The proof of Theorem 4.3 uses it only after establishing $\lambda_k=\lambda_{k+1}$, so the hypothesis is added. Eigenvalues are 0-based in Lean: $\lambda_k$ is `eig B ⟨k-1,_⟩`.
-- source:
--   Pataki, On the rank of extreme matrices in semidefinite programs and the multiplicity of optimal eigenvalues, Math. Oper. Res. 23(2) (1998), p. 348, §3, display after the definition of Ω_k(B)

import Mathlib
import Definitions.Def_BurerMonteiro_RankIncrease_SDP
import Definitions.Def_ProjLikeRetr_Spectral_SpectralSet
import Definitions.Def_PatakiRank_Mult_Setting
open Matrix BurerMonteiro.RankIncrease ProjLikeRetr.Spectral

namespace PatakiRank.Mult

/-- The rank identity of §3 (p. 348), in the case `λ_k(B) = λ_{k+1}(B)` (the only case in which
it holds and the case used in the proof of Theorem 4.3): for `(z, V, W) ∈ Ω_k(B)` with
`z = ½(λ_k(B) + λ_{k+1}(B))`, `rank V + rank W + mult(λ_k(B)) = n`. -/
theorem rank_identity {n k : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm)
    (hk : 1 ≤ k) (hkn : k < n)
    (heq : eig B ⟨k - 1, by omega⟩ = eig B ⟨k, hkn⟩)
    (p : ℝ × Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) (hp : p ∈ Omega k B)
    (hz : p.1 = (1 / 2 : ℝ) * (eig B ⟨k - 1, by omega⟩ + eig B ⟨k, hkn⟩)) :
    p.2.1.rank + p.2.2.rank + mult B ⟨k - 1, by omega⟩ = n := by sorry

end PatakiRank.Mult
