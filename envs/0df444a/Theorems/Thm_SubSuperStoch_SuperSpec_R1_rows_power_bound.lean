-- Prove2me | Theorems.Thm_SubSuperStoch_SuperSpec_R1_rows_power_bound
-- name    : SubSuperStoch.SuperSpec.R1_rows_power_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:26:43.812847+00:00
-- url     : https://prove2.me/theorems/9005d000-6041-4f2c-8415-1ab007cbeeac
-- title:
--   Proof of Theorem 2.6, p. 9 — Λ_i[F^{|C*|+1}] ≤ α₃^{|C*|+1} − (α₃ − α₁)α₂^{|C*|} < 1 for every row i of sum < 1
-- statement:
--   Let $F$ be an $n\times n$ super-stochastic matrix and put
--   $$\alpha_1=\max\{\Lambda_s[F]\mid \Lambda_s[F]<1\},\quad \alpha_2=\min\{[F]_{ij}\mid [F]_{ij}>0\},\quad \alpha_3=\max\{\Lambda_s[F]\mid\Lambda_s[F]\ge 1\},$$
--   all three sets being non-empty. Let $C$ be a natural number (in Theorem 2.6, $C=|\mathcal C^*|$) satisfying condition (2.5),
--   $$\sqrt[C]{\alpha_3^{C+1}-(\alpha_3-\alpha_1)\alpha_2^{C}}<1.$$
--   Then for every row $i$ with $\Lambda_i[F]<1$,
--   $$\Lambda_i[F^{C+1}]\le \alpha_3^{C+1}-(\alpha_3-\alpha_1)\alpha_2^{C}<1.$$
--
--   This is the third step of the proof of Theorem 2.6: the rows of sum less than one need no chain, because their own deficit already gives the bound.
--
--   **Formalization Note** The page writes the identity $\Lambda_i[F^{|\mathcal C^*|+1}]=\sum_j[F]_{ij}\Lambda_j[F^{|\mathcal C^*|}]$ before the inequality; the statement keeps only the inequality and the final "$<1$". No chain hypothesis is assumed and $C$ is an arbitrary natural number, since the bound holds for every $C$; the root is the real power $x^{1/C}$.
-- source:
--   Shi, Zheng, Shao, Cheng, arXiv:2004.01867v2, p. 9, proof of Theorem 2.6, third display; condition (2.5)

import Mathlib
import Definitions.Def_SubSuperStoch_SuperSpec_Setting

namespace SubSuperStoch.SuperSpec

theorem R1_rows_power_bound {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ)
    (hF : IsSuperStochastic F)
    (α₁ : ℝ) (hα₁ : IsGreatest {x | ∃ s, SubSuperStoch.SubSpec.rowSum F s < 1 ∧ x = SubSuperStoch.SubSpec.rowSum F s} α₁)
    (α₂ : ℝ) (hα₂ : IsLeast {x | ∃ i j, 0 < F i j ∧ x = F i j} α₂)
    (α₃ : ℝ) (hα₃ : IsGreatest {x | ∃ s, 1 ≤ SubSuperStoch.SubSpec.rowSum F s ∧ x = SubSuperStoch.SubSpec.rowSum F s} α₃)
    (C : ℕ) (h25 : (α₃ ^ (C + 1) - (α₃ - α₁) * α₂ ^ C) ^ (1 / (C : ℝ)) < 1) :
    ∀ i, SubSuperStoch.SubSpec.rowSum F i < 1 →
      SubSuperStoch.SubSpec.rowSum (F ^ (C + 1)) i ≤ α₃ ^ (C + 1) - (α₃ - α₁) * α₂ ^ C ∧
        α₃ ^ (C + 1) - (α₃ - α₁) * α₂ ^ C < 1 := by sorry

end SubSuperStoch.SuperSpec
