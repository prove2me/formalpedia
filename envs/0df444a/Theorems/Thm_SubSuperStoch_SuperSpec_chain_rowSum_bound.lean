-- Prove2me | Theorems.Thm_SubSuperStoch_SuperSpec_chain_rowSum_bound
-- name    : SubSuperStoch.SuperSpec.chain_rowSum_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:26:13.228497+00:00
-- url     : https://prove2.me/theorems/9a6faa3f-7c06-4dd9-a637-f192f764fe41
-- title:
--   Proof of Theorem 2.6, p. 9 — along a chain from a row of sum < 1, Λ_k[F^{r+2}] ≤ α₃^{r+2} − (α₃ − α₁)α₂^{r+1}
-- statement:
--   Let $F$ be an $n\times n$ super-stochastic matrix. Put
--   $$\alpha_1=\max\{\Lambda_s[F]\mid \Lambda_s[F]<1\},\qquad \alpha_2=\min\{[F]_{ij}\mid [F]_{ij}>0\},\qquad \alpha_3=\max\{\Lambda_s[F]\mid\Lambda_s[F]\ge 1\},$$
--   all three sets being non-empty. Let $i$ be a row with $\Lambda_i[F]<1$, and let $[F]_{ki_r},\dots,[F]_{i_2i_1},[F]_{i_1i}$ be a non-zero element chain of $r+1\ge 1$ elements from $i$ to $k$ (every listed entry non-zero, consecutive indices distinct). Then
--   $$\Lambda_k[F^{r+2}]\le \alpha_3^{r+2}-(\alpha_3-\alpha_1)\alpha_2^{r+1}.$$
--
--   This is the first step of the proof of Theorem 2.6: the deficit of the starting row is carried along the chain, so that the end row $k$ of the chain has a row sum of $F^{r+2}$ strictly below the trivial bound $\alpha_3^{r+2}$.
--
--   **Formalization Note** The chain is a function $c:\mathbb N\to\{1,\dots,n\}$ with $c_0=i$, $c_L=k$, $L=r+1\ge 1$. The maxima and the minimum are passed as values $\alpha_1,\alpha_2,\alpha_3$ together with the hypotheses that each is the greatest (least) element of exactly the printed set. The page states this for $k\in\mathcal R_2$; the bound does not use $\Lambda_k[F]\ge1$, so that hypothesis is not imposed.
-- source:
--   Shi, Zheng, Shao, Cheng, arXiv:2004.01867v2, p. 9, proof of Theorem 2.6, first display (α₁, α₂ as in Theorem 2.2, p. 5; α₃ as in Theorem 2.6)

import Mathlib
import Definitions.Def_SubSuperStoch_SuperSpec_Setting

namespace SubSuperStoch.SuperSpec

theorem chain_rowSum_bound {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ)
    (hF : IsSuperStochastic F)
    (α₁ : ℝ) (hα₁ : IsGreatest {x | ∃ s, SubSuperStoch.SubSpec.rowSum F s < 1 ∧ x = SubSuperStoch.SubSpec.rowSum F s} α₁)
    (α₂ : ℝ) (hα₂ : IsLeast {x | ∃ i j, 0 < F i j ∧ x = F i j} α₂)
    (α₃ : ℝ) (hα₃ : IsGreatest {x | ∃ s, 1 ≤ SubSuperStoch.SubSpec.rowSum F s ∧ x = SubSuperStoch.SubSpec.rowSum F s} α₃)
    (i : Fin n) (hi : SubSuperStoch.SubSpec.rowSum F i < 1)
    (c : ℕ → Fin n) (L : ℕ) (hc0 : c 0 = i) (hL : 1 ≤ L) (hc : SubSuperStoch.SubSpec.IsChain F c L) :
    SubSuperStoch.SubSpec.rowSum (F ^ (L + 1)) (c L) ≤ α₃ ^ (L + 1) - (α₃ - α₁) * α₂ ^ L := by sorry

end SubSuperStoch.SuperSpec
