-- Prove2me | Theorems.Thm_SubSuperStoch_SubSpec_chain_rowSum_bound
-- name    : SubSuperStoch.SubSpec.chain_rowSum_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:31:24.901534+00:00
-- url     : https://prove2.me/theorems/ac1a60b4-0665-45fb-9da7-31137fbe403c
-- title:
--   Proof of Theorem 2.2, p. 5 — at the end of a chain of L non-zero entries, Λ_k[F^{L+1}] ≤ 1 − (1 − α₁)α₂^L < 1
-- statement:
--   Let $F$ be an $n\times n$ sub-stochastic matrix. Let
--   $$\alpha_1=\max\{\Lambda_s[F]\mid \Lambda_s[F]<1\},\qquad \alpha_2=\min\{[F]_{ij}>0\mid i,j=1,\dots,n\}$$
--   be the largest row sum below one and the smallest positive entry of $F$ (both sets are assumed non-empty). Let $i$ be a row with $\Lambda_i[F]<1$, and let $[F]_{k i_r},\dots,[F]_{i_2 i_1},[F]_{i_1 i}$ be a non-zero element chain from $i$ to $k$ with $L=r+1\ge 1$ elements. Then
--   $$\Lambda_k[F^{L+1}]\le 1-(1-\alpha_1)\alpha_2^{L}<1 .$$
--   In the paper's indexing ($L=r+1$) this is $\Lambda_k[F^{r+2}]\le 1-(1-\alpha_1)\alpha_2^{r+1}<1$; the cases $L=1,2$ are the displayed bounds $\Lambda_{i_1}[F^2]\le 1-(1-\alpha_1)\alpha_2$ and $\Lambda_{i_2}[F^3]\le 1-(1-\alpha_1)\alpha_2^2$.
--
--   This is the first step of the proof of Theorem 2.2: the deficit $1-\Lambda_i[F]$ of a row of sum below one propagates along the chain, shrinking by at most a factor $\alpha_2$ per entry.
--
--   **Formalization Note** The chain is `c : ℕ → Fin n` with `c 0 = i`, `1 ≤ L` and `IsChain F c L`; its endpoint $k$ is `c L`. The maxima and minimum are passed as values with `IsGreatest`/`IsLeast` hypotheses over exactly the printed sets.
-- source:
--   Shi, Zheng, Shao, Cheng, arXiv:2004.01867v2, p. 5, proof of Theorem 2.2 (first block of displays, Λ_{i₁}[F²], Λ_{i₂}[F³], …, Λ_k[F^{r+2}])

import Mathlib
import Definitions.Def_SubSuperStoch_SubSpec_Setting

namespace SubSuperStoch.SubSpec

theorem chain_rowSum_bound {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) (hF : IsSubStochastic F)
    (α₁ : ℝ) (hα₁ : IsGreatest {x | ∃ s, rowSum F s < 1 ∧ x = rowSum F s} α₁)
    (α₂ : ℝ) (hα₂ : IsLeast {x | ∃ i j, 0 < F i j ∧ x = F i j} α₂)
    (i : Fin n) (hi : rowSum F i < 1)
    (c : ℕ → Fin n) (L : ℕ) (hc0 : c 0 = i) (hL : 1 ≤ L) (hc : IsChain F c L) :
    rowSum (F ^ (L + 1)) (c L) ≤ 1 - (1 - α₁) * α₂ ^ L ∧ 1 - (1 - α₁) * α₂ ^ L < 1 := by sorry

end SubSuperStoch.SubSpec
