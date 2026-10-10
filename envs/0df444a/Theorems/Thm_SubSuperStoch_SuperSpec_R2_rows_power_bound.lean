-- Prove2me | Theorems.Thm_SubSuperStoch_SuperSpec_R2_rows_power_bound
-- name    : SubSuperStoch.SuperSpec.R2_rows_power_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:26:07.174104+00:00
-- url     : https://prove2.me/theorems/a67e69a9-718d-4cc9-9f0b-f42f0136dbd8
-- title:
--   Proof of Theorem 2.6, p. 9 — Λ_k[F^{|C*|+1}] ≤ α₃^{|C*|+1} − (α₃ − α₁)α₂^{|C*|} < 1 for every row k of sum ≥ 1
-- statement:
--   Let $F$ be an $n\times n$ super-stochastic matrix, and let $\mathcal R_1=\{s\mid\Lambda_s[F]<1\}$ and $\mathcal R_2=\{s\mid\Lambda_s[F]\ge1\}$ be non-empty. Suppose that for each $k\in\mathcal R_2$ a non-zero element chain $\mathcal C_{i\to k}=[F]_{ki_r},\dots,[F]_{i_2i_1},[F]_{i_1i}$ with $i\in\mathcal R_1$ is given, and let $|\mathcal C^*|$ be the largest number of elements of these chains. With
--   $$\alpha_1=\max\{\Lambda_s[F]\mid \Lambda_s[F]<1\},\quad \alpha_2=\min\{[F]_{ij}\mid [F]_{ij}>0\},\quad \alpha_3=\max\{\Lambda_s[F]\mid\Lambda_s[F]\ge 1\},$$
--   assume condition (2.5):
--   $$\sqrt[|\mathcal C^*|]{\alpha_3^{|\mathcal C^*|+1}-(\alpha_3-\alpha_1)\alpha_2^{|\mathcal C^*|}}<1.$$
--   Then for every $k\in\mathcal R_2$,
--   $$\Lambda_k[F^{|\mathcal C^*|+1}]\le \alpha_3^{|\mathcal C^*|+1}-(\alpha_3-\alpha_1)\alpha_2^{|\mathcal C^*|}<1.$$
--
--   This is the second step of the proof of Theorem 2.6: it lifts the chain bound from $F^{r+2}$ to the common power $F^{|\mathcal C^*|+1}$ for every row of sum at least one.
--
--   **Formalization Note** The chosen chains are given by a length function $\mathrm{len}$ on rows: for each $k\in\mathcal R_2$ there are $i\in\mathcal R_1$ and a chain from $i$ to $k$ of $\mathrm{len}(k)\ge1$ elements, and $|\mathcal C^*|=C$ is the greatest of $\mathrm{len}(k)$ over $k\in\mathcal R_2$. The $|\mathcal C^*|$-th root is the real power $x^{1/C}$; its radicand is nonnegative under the hypotheses ($\alpha_2\le\alpha_3$ and $\alpha_1\ge0$), and since $C\ge1$ condition (2.5) is equivalent to $\alpha_3^{C+1}-(\alpha_3-\alpha_1)\alpha_2^{C}<1$.
-- source:
--   Shi, Zheng, Shao, Cheng, arXiv:2004.01867v2, p. 9, proof of Theorem 2.6, second display; condition (2.5)

import Mathlib
import Definitions.Def_SubSuperStoch_SuperSpec_Setting

namespace SubSuperStoch.SuperSpec

theorem R2_rows_power_bound {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) (hF : IsSuperStochastic F)
    (hR₁ : ∃ s, SubSuperStoch.SubSpec.rowSum F s < 1) (hR₂ : ∃ s, 1 ≤ SubSuperStoch.SubSpec.rowSum F s)
    (len : Fin n → ℕ)
    (hchain : ∀ k, 1 ≤ SubSuperStoch.SubSpec.rowSum F k → ∃ i, SubSuperStoch.SubSpec.rowSum F i < 1 ∧
      ∃ c : ℕ → Fin n, c 0 = i ∧ c (len k) = k ∧ 1 ≤ len k ∧ SubSuperStoch.SubSpec.IsChain F c (len k))
    (α₁ : ℝ) (hα₁ : IsGreatest {x | ∃ s, SubSuperStoch.SubSpec.rowSum F s < 1 ∧ x = SubSuperStoch.SubSpec.rowSum F s} α₁)
    (α₂ : ℝ) (hα₂ : IsLeast {x | ∃ i j, 0 < F i j ∧ x = F i j} α₂)
    (α₃ : ℝ) (hα₃ : IsGreatest {x | ∃ s, 1 ≤ SubSuperStoch.SubSpec.rowSum F s ∧ x = SubSuperStoch.SubSpec.rowSum F s} α₃)
    (C : ℕ) (hC : IsGreatest {m | ∃ k, 1 ≤ SubSuperStoch.SubSpec.rowSum F k ∧ m = len k} C)
    (h25 : (α₃ ^ (C + 1) - (α₃ - α₁) * α₂ ^ C) ^ (1 / (C : ℝ)) < 1) :
    ∀ k, 1 ≤ SubSuperStoch.SubSpec.rowSum F k →
      SubSuperStoch.SubSpec.rowSum (F ^ (C + 1)) k ≤ α₃ ^ (C + 1) - (α₃ - α₁) * α₂ ^ C ∧
        α₃ ^ (C + 1) - (α₃ - α₁) * α₂ ^ C < 1 := by sorry

end SubSuperStoch.SuperSpec
