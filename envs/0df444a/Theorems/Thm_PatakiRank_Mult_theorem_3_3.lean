-- Prove2me | Theorems.Thm_PatakiRank_Mult_theorem_3_3
-- name    : PatakiRank.Mult.theorem_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:26:47.66108+00:00
-- url     : https://prove2.me/theorems/3a583d4b-fa8d-4e88-974d-0264f38ff9dc
-- title:
--   Theorem 3.3, p. 347 — optimal solutions of the SDP (3.14): λ_{k+1} ≤ z* ≤ λ_k, V* = Q Diag v* Qᵀ, W* = Q Diag w* Qᵀ
-- statement:
--   Let $B$ be an $n\times n$ symmetric matrix and write $B=Q\Lambda Q^T$ with $Q$ an orthonormal $n\times n$ matrix ($Q^TQ=I$) and $\Lambda=\operatorname{diag}\lambda$, $\lambda_1\ge\dots\ge\lambda_n$. Let $1\le k<n$. The SDP
--   $$\min\ kz+I\bullet V\quad\text{s.t.}\quad V,W\succeq0,\quad zI+V-W=B \tag{3.14}$$
--   has optimal value $\sum_{i=1}^k\lambda_i$ (attained), and $(z^*,V^*,W^*)$ is optimal if and only if
--   $$\lambda_{k+1}\le z^*\le\lambda_k,\qquad V^*=Q(\operatorname{Diag}v^*)Q^T,\qquad W^*=Q(\operatorname{Diag}w^*)Q^T,$$
--   where $v^*=(\lambda_1-z^*,\dots,\lambda_k-z^*,0,\dots,0)^T$ and $w^*=(0,\dots,0,z^*-\lambda_{k+1},\dots,z^*-\lambda_n)^T$.
--
--   The optimal value is $f_k(B)$, the sum of the $k$ largest eigenvalues of $B$, and the theorem describes the whole optimal set $\Omega_k(B)$: a segment when $\lambda_k>\lambda_{k+1}$ and a single point otherwise. This explicit description is what the multiplicity bounds of §4 are built on.
--
--   **Formalization Note** The decomposition is a hypothesis ($Q^TQ=I$, $\lambda$ nonincreasing, $B=Q\operatorname{Diag}(\lambda)Q^T$); symmetry of $B$ follows from it. The optimal value is stated as a least element of the set of feasible objective values. $1\le k<n$ is assumed because the statement uses $\lambda_{k+1}$.
-- source:
--   Pataki, On the rank of extreme matrices in semidefinite programs and the multiplicity of optimal eigenvalues, Math. Oper. Res. 23(2) (1998), p. 347, Theorem 3.3 ((3.23)–(3.25))

import Mathlib
import Definitions.Def_BurerMonteiro_RankIncrease_SDP
import Definitions.Def_ProjLikeRetr_Spectral_SpectralSet
import Definitions.Def_PatakiRank_Mult_Setting
open Matrix BurerMonteiro.RankIncrease ProjLikeRetr.Spectral

namespace PatakiRank.Mult

/-- Theorem 3.3 (p. 347): write `B = Q Λ Qᵀ` with `Q` orthonormal, `Λ = diag λ`,
`λ₁ ≥ ⋯ ≥ λ_n`. The SDP (3.14) has optimal value `∑_{i ≤ k} λ_i`, and `(z*, V*, W*)` is optimal
iff (3.23) `λ_{k+1} ≤ z* ≤ λ_k` and (3.24) `V* = Q (Diag v*) Qᵀ`, `W* = Q (Diag w*) Qᵀ`, with
`v*, w*` as in (3.25). -/
theorem theorem_3_3 {n k : ℕ} (B Q : Matrix (Fin n) (Fin n) ℝ) (lam : Fin n → ℝ)
    (hQ : Qᵀ * Q = 1) (hlam : Antitone lam) (hB : B = Q * diagonal lam * Qᵀ)
    (hk : 1 ≤ k) (hkn : k < n) :
    IsLeast (sdpObj k '' {p | sdpFeas B p}) (∑ i : Fin n with i.val < k, lam i) ∧
    ∀ p : ℝ × Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ,
      IsOptimal (sdpFeas B) (sdpObj k) p ↔
        ((lam ⟨k, hkn⟩ ≤ p.1 ∧ p.1 ≤ lam ⟨k - 1, by omega⟩) ∧
          p.2.1 = Q * diagonal (vStar k lam p.1) * Qᵀ ∧
          p.2.2 = Q * diagonal (wStar k lam p.1) * Qᵀ) := by sorry

end PatakiRank.Mult
