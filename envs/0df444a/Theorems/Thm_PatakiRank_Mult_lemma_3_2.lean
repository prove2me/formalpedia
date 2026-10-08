-- Prove2me | Theorems.Thm_PatakiRank_Mult_lemma_3_2
-- name    : PatakiRank.Mult.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:26:23.700397+00:00
-- url     : https://prove2.me/theorems/ac6fd998-6658-4933-a705-cc0425782aea
-- title:
--   Lemma 3.2, pp. 346–347 — the diagonal SDP (3.21): value Σ_{i≤k} λ_i, optimal iff V* = Diag v*, W* = Diag w*
-- statement:
--   Let $\lambda\in\mathbb R^n$ with $\lambda_1\ge\dots\ge\lambda_n$, let $1\le k<n$, and let $\Lambda=\operatorname{Diag}\lambda$. Consider the semidefinite program
--   $$\min\ kz+I\bullet V\quad\text{s.t.}\quad V,W\succeq0,\quad zI+V-W=\Lambda \tag{3.21}$$
--   over $(z,V,W)\in\mathbb R\times\mathcal S^n\times\mathcal S^n$. Its optimal value is $\sum_{i=1}^k\lambda_i$ (attained), and $(z^*,V^*,W^*)$ is optimal if and only if $V^*=\operatorname{Diag}v^*$ and $W^*=\operatorname{Diag}w^*$ with
--   $$\lambda_{k+1}\le z^*\le\lambda_k,\qquad v^*=(\lambda_1-z^*,\dots,\lambda_k-z^*,0,\dots,0)^T,\qquad w^*=(0,\dots,0,z^*-\lambda_{k+1},\dots,z^*-\lambda_n)^T.$$
--
--   It removes the diagonality restriction on $V,W$ from Lemma 3.1, keeping it on the data.
--
--   **Formalization Note** (3.21) is the SDP (3.14) with $B=\operatorname{Diag}\lambda$. The optimal value is stated as a least element of the set of feasible objective values, and $1\le k<n$ is assumed as in Lemma 3.1.
-- source:
--   Pataki, On the rank of extreme matrices in semidefinite programs and the multiplicity of optimal eigenvalues, Math. Oper. Res. 23(2) (1998), pp. 346–347, Lemma 3.2 ((3.21))

import Mathlib
import Definitions.Def_BurerMonteiro_RankIncrease_SDP
import Definitions.Def_ProjLikeRetr_Spectral_SpectralSet
import Definitions.Def_PatakiRank_Mult_Setting
open Matrix BurerMonteiro.RankIncrease ProjLikeRetr.Spectral

namespace PatakiRank.Mult

/-- Lemma 3.2 (pp. 346–347): for `λ₁ ≥ ⋯ ≥ λ_n` and `Λ = Diag λ`, the SDP (3.21)
`min {k z + I • V : V, W ⪰ 0, z I + V − W = Λ}` has optimal value `∑_{i ≤ k} λ_i`, and
`(z*, V*, W*)` is optimal iff `V* = Diag v*`, `W* = Diag w*` with `(z*, v*, w*)` as in (3.19),
(3.20). -/
theorem lemma_3_2 {n k : ℕ} (lam : Fin n → ℝ) (hlam : Antitone lam) (hk : 1 ≤ k) (hkn : k < n) :
    IsLeast (sdpObj k '' {p | sdpFeas (diagonal lam) p}) (∑ i : Fin n with i.val < k, lam i) ∧
    ∀ p : ℝ × Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ,
      IsOptimal (sdpFeas (diagonal lam)) (sdpObj k) p ↔
        ((lam ⟨k, hkn⟩ ≤ p.1 ∧ p.1 ≤ lam ⟨k - 1, by omega⟩) ∧
          p.2.1 = diagonal (vStar k lam p.1) ∧ p.2.2 = diagonal (wStar k lam p.1)) := by sorry

end PatakiRank.Mult
