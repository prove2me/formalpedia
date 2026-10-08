-- Prove2me | Theorems.Thm_PatakiRank_Mult_lemma_3_1
-- name    : PatakiRank.Mult.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:26:34.712466+00:00
-- url     : https://prove2.me/theorems/ad0936e1-ceab-41d0-8b9f-45a4e3fe3a7b
-- title:
--   Lemma 3.1, p. 346 — the LP (3.18) has value Σ_{i≤k} λ_i, optimal iff (3.19)–(3.20)
-- statement:
--   Let $\lambda\in\mathbb R^n$ with $\lambda_1\ge\dots\ge\lambda_n$, let $1\le k<n$, and let $e$ be the all-ones vector. Consider the linear program
--   $$\min\ kz+e^Tv\quad\text{s.t.}\quad v,w\ge0,\quad ze+v-w=\lambda \tag{3.18}$$
--   over $(z,v,w)\in\mathbb R\times\mathbb R^n\times\mathbb R^n$. Its optimal value is $\sum_{i=1}^k\lambda_i$ (attained), and $(z^*,v^*,w^*)$ is an optimal solution if and only if
--   $$\lambda_{k+1}\le z^*\le\lambda_k,\qquad v^*=(\lambda_1-z^*,\dots,\lambda_k-z^*,0,\dots,0)^T,\qquad w^*=(0,\dots,0,z^*-\lambda_{k+1},\dots,z^*-\lambda_n)^T.$$
--
--   This diagonal case is the first step towards the explicit description of the optimal solutions of the SDP (3.14), whose value is $f_k(B)$.
--
--   **Formalization Note** "Optimal value is $\sum_{i\le k}\lambda_i$" is stated as: this number is the least element of the set of objective values of feasible points. "Optimal" means feasible and no worse than every feasible point; the equivalence is stated for all triples (the right-hand side implies feasibility). The paper allows $k\in\{1,\dots,n\}$ but the statement uses $\lambda_{k+1}$, so $1\le k<n$ is assumed (the standing case $k<n$ of §4).
-- source:
--   Pataki, On the rank of extreme matrices in semidefinite programs and the multiplicity of optimal eigenvalues, Math. Oper. Res. 23(2) (1998), p. 346, Lemma 3.1 ((3.18)–(3.20))

import Mathlib
import Definitions.Def_BurerMonteiro_RankIncrease_SDP
import Definitions.Def_ProjLikeRetr_Spectral_SpectralSet
import Definitions.Def_PatakiRank_Mult_Setting
open Matrix BurerMonteiro.RankIncrease ProjLikeRetr.Spectral

namespace PatakiRank.Mult

/-- Lemma 3.1 (p. 346): for `λ₁ ≥ ⋯ ≥ λ_n`, the LP (3.18) `min {k z + eᵀv : v, w ≥ 0,
z e + v − w = λ}` has optimal value `∑_{i ≤ k} λ_i`, and `(z*, v*, w*)` is optimal iff (3.19)
`λ_{k+1} ≤ z* ≤ λ_k` and (3.20) `v* = (λ₁ − z*, …, λ_k − z*, 0, …, 0)ᵀ`,
`w* = (0, …, 0, z* − λ_{k+1}, …, z* − λ_n)ᵀ`. -/
theorem lemma_3_1 {n k : ℕ} (lam : Fin n → ℝ) (hlam : Antitone lam) (hk : 1 ≤ k) (hkn : k < n) :
    IsLeast (lpObj k '' {p | lpFeas lam p}) (∑ i : Fin n with i.val < k, lam i) ∧
    ∀ p : ℝ × (Fin n → ℝ) × (Fin n → ℝ), IsOptimal (lpFeas lam) (lpObj k) p ↔
      ((lam ⟨k, hkn⟩ ≤ p.1 ∧ p.1 ≤ lam ⟨k - 1, by omega⟩) ∧
        p.2.1 = vStar k lam p.1 ∧ p.2.2 = wStar k lam p.1) := by sorry

end PatakiRank.Mult
