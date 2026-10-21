-- Prove2me | Theorems.Thm_TradingFavors_Existence_lemma_2
-- name    : TradingFavors.Existence.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:28:14.031094+00:00
-- url     : https://prove2.me/theorems/b82adc58-72e1-4472-9b0d-727e853fc1a2
-- title:
--   Lemma 2, pp. 11–12 (PDF 11–12) — the payoffs solve the balance system (6) and Bᵢ(k|σ) is invertible
-- statement:
--   Fix parameters satisfying the standing assumptions, a trading-favors strategy profile $\sigma$ and a balance $k\in\mathbb Z$. For firm $i$ with partner $j$, collect firm $i$'s payoffs in cluster $k$ into the vector $\Pi_i(k)=(\pi_i(0,0,k\mid\sigma),\pi_i(1,0,k\mid\sigma),\pi_i(0,1,k\mid\sigma),\pi_i(1,1,k\mid\sigma))^\top$ (own state first) and the reward rates into $R_i(k\mid\sigma)=(\mathcal R_i(0,0,k\mid\sigma),\dots,\mathcal R_i(1,1,k\mid\sigma))^\top$. Then
--
--   1. the matrix $B_i(k\mid\sigma)$ is invertible, for $i=1,2$;
--   2. the payoffs satisfy
--   $$
--   B_i(k\mid\sigma)\,\Pi_i(k)=R_i(k\mid\sigma)+\begin{pmatrix}0&0\\ \lambda_i(1-\sigma_j(k))&0\\ 0&\lambda_j(1-\sigma_i(k))\\ 0&0\end{pmatrix}\begin{pmatrix}v_i(k-(-1)^j\mid\sigma)\\ v_i(k-(-1)^i\mid\sigma)\end{pmatrix},
--   $$
--   where $v_i(k\mid\sigma)=\pi_i(1,1,k\mid\sigma)$. For firm 1 the two neighbours are $v_1(k-1)$ and $v_1(k+1)$; for firm 2 they are $v_2(k+1)$ and $v_2(k-1)$.
--
--   This is the balance system (5) written cluster by cluster: firm $i$'s four payoffs in cluster $k$ are affine functions of the two neighbouring values $v_i(k\pm1)$, which is what the recursions of Lemma 3 are built on.
--
--   **Formalization Note** The matrix-vector product is written out (`*ᵥ`), with the product of the $4\times2$ matrix and the 2-vector expanded. Invertibility is stated as `IsUnit det`. Firm 2's matrix and vectors are in firm 2's own coordinates $(x_2,x_1)$.
-- source:
--   Hu & Caldentey, Trust and Reciprocity in Firms’ Capacity Sharing, SSRN 4348127 (version of February 6, 2023), pp. 11–12 (PDF 11–12), Lemma 2, eqs. (5)–(6)

import Mathlib
import Definitions.Def_TradingFavors_Existence_Model

namespace TradingFavors.Existence

open Matrix

theorem lemma_2 (θ : Params) (hθ : θ.Standing) (σ : Profile) (k : ℤ) :
    IsUnit (B1 θ (fr (σ.s1 k)) (fr (σ.s2 k))).det ∧
    IsUnit (B2 θ (fr (σ.s1 k)) (fr (σ.s2 k))).det ∧
    B1 θ (fr (σ.s1 k)) (fr (σ.s2 k)) *ᵥ
        ![pi1 θ σ 0 0 k, pi1 θ σ 1 0 k, pi1 θ σ 0 1 k, pi1 θ σ 1 1 k] =
      R1vec θ σ k +
        ![0, θ.lam1 * (1 - fr (σ.s2 k)) * v1 θ σ (k - 1),
          θ.lam2 * (1 - fr (σ.s1 k)) * v1 θ σ (k + 1), 0] ∧
    B2 θ (fr (σ.s1 k)) (fr (σ.s2 k)) *ᵥ
        ![pi2 θ σ 0 0 k, pi2 θ σ 1 0 k, pi2 θ σ 0 1 k, pi2 θ σ 1 1 k] =
      R2vec θ σ k +
        ![0, θ.lam2 * (1 - fr (σ.s1 k)) * v2 θ σ (k + 1),
          θ.lam1 * (1 - fr (σ.s2 k)) * v2 θ σ (k - 1), 0] := by sorry

end TradingFavors.Existence
