-- Prove2me | Theorems.Thm_SubSuperStoch_SuperSpec_normInf_power_bound
-- name    : SubSuperStoch.SuperSpec.normInf_power_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:26:56.34525+00:00
-- url     : https://prove2.me/theorems/c31a5ba7-a8b3-4fff-b1a5-e350e6d2141c
-- title:
--   Proof of Theorem 2.6, p. 9 — ‖F^{|C*|+1}‖_∞ ≤ α₃^{|C*|+1} − (α₃ − α₁)α₂^{|C*|} < 1
-- statement:
--   Under the hypotheses of Theorem 2.6 — $F$ an $n\times n$ super-stochastic matrix, $\mathcal R_1=\{s\mid\Lambda_s[F]<1\}$ and $\mathcal R_2=\{s\mid\Lambda_s[F]\ge1\}$ non-empty, a non-zero element chain $\mathcal C_{i\to k}$ from some $i\in\mathcal R_1$ for each $k\in\mathcal R_2$, $|\mathcal C^*|$ the largest number of elements of these chains, $\alpha_1,\alpha_2,\alpha_3$ as in Theorem 2.6, and condition (2.5) —
--   $$\|F^{|\mathcal C^*|+1}\|_\infty\le \alpha_3^{|\mathcal C^*|+1}-(\alpha_3-\alpha_1)\alpha_2^{|\mathcal C^*|}<1.$$
--
--   This is the fourth step of the proof of Theorem 2.6: the row bounds for $\mathcal R_1$ and $\mathcal R_2$ together bound every row sum of the nonnegative matrix $F^{|\mathcal C^*|+1}$, hence its infinity norm.
--
--   **Formalization Note** The hypotheses are exactly those of the goal theorem `theorem_2_6`, with the chosen chains given by a length function and $|\mathcal C^*|$ its greatest value over $\mathcal R_2$. The infinity norm is the maximal absolute row sum over the index type `Fin n`.
-- source:
--   Shi, Zheng, Shao, Cheng, arXiv:2004.01867v2, p. 9, proof of Theorem 2.6, fourth display

import Mathlib
import Definitions.Def_SubSuperStoch_SuperSpec_Setting

namespace SubSuperStoch.SuperSpec

theorem normInf_power_bound {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) (hF : IsSuperStochastic F)
    (hR₁ : ∃ s, SubSuperStoch.SubSpec.rowSum F s < 1) (hR₂ : ∃ s, 1 ≤ SubSuperStoch.SubSpec.rowSum F s)
    (len : Fin n → ℕ)
    (hchain : ∀ k, 1 ≤ SubSuperStoch.SubSpec.rowSum F k → ∃ i, SubSuperStoch.SubSpec.rowSum F i < 1 ∧
      ∃ c : ℕ → Fin n, c 0 = i ∧ c (len k) = k ∧ 1 ≤ len k ∧ SubSuperStoch.SubSpec.IsChain F c (len k))
    (α₁ : ℝ) (hα₁ : IsGreatest {x | ∃ s, SubSuperStoch.SubSpec.rowSum F s < 1 ∧ x = SubSuperStoch.SubSpec.rowSum F s} α₁)
    (α₂ : ℝ) (hα₂ : IsLeast {x | ∃ i j, 0 < F i j ∧ x = F i j} α₂)
    (α₃ : ℝ) (hα₃ : IsGreatest {x | ∃ s, 1 ≤ SubSuperStoch.SubSpec.rowSum F s ∧ x = SubSuperStoch.SubSpec.rowSum F s} α₃)
    (C : ℕ) (hC : IsGreatest {m | ∃ k, 1 ≤ SubSuperStoch.SubSpec.rowSum F k ∧ m = len k} C)
    (h25 : (α₃ ^ (C + 1) - (α₃ - α₁) * α₂ ^ C) ^ (1 / (C : ℝ)) < 1) :
    SubSuperStoch.SubSpec.normInf (F ^ (C + 1)) ≤ α₃ ^ (C + 1) - (α₃ - α₁) * α₂ ^ C ∧
      α₃ ^ (C + 1) - (α₃ - α₁) * α₂ ^ C < 1 := by sorry

end SubSuperStoch.SuperSpec
