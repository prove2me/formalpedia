-- Prove2me | Theorems.Thm_SubSuperStoch_SubSpec_deficient_rows_power_bound
-- name    : SubSuperStoch.SubSpec.deficient_rows_power_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:31:28.751586+00:00
-- url     : https://prove2.me/theorems/f54963f7-dfe8-448b-aa91-0300a7f3ded4
-- title:
--   Proof of Theorem 2.2, p. 5 — Λ_i[F^{|C*|+1}] ≤ 1 − (1 − α₁)α₂^{|C*|} < 1 for every row i ∈ S₁
-- statement:
--   Let $F$ be an $n\times n$ sub-stochastic matrix, and let $\alpha_1=\max\{\Lambda_s[F]\mid\Lambda_s[F]<1\}$ and $\alpha_2=\min\{[F]_{ij}>0\mid i,j=1,\dots,n\}$ (both sets non-empty). For every natural number $C$ (in the paper, $C=|\mathcal C^*|$) and every row $i$ with $\Lambda_i[F]<1$,
--   $$\Lambda_i\big[F^{C+1}\big]\le 1-(1-\alpha_1)\alpha_2^{C}<1.$$
--
--   In the proof of Theorem 2.2 this is the bound for the rows of $\mathcal S_1$; together with the bound for the rows of $\mathcal S_2$ it controls every row of $F^{|\mathcal C^*|+1}$.
--
--   **Formalization Note** The page states this for $C=|\mathcal C^*|$; the argument does not use the chains, so the statement is given for an arbitrary natural number $C$, which contains the page's case.
-- source:
--   Shi, Zheng, Shao, Cheng, arXiv:2004.01867v2, p. 5, proof of Theorem 2.2 (display Λ_i[F^{|C*|+1}] after "In addition, for any i ∈ S₁")

import Mathlib
import Definitions.Def_SubSuperStoch_SubSpec_Setting

namespace SubSuperStoch.SubSpec

theorem deficient_rows_power_bound {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) (hF : IsSubStochastic F)
    (α₁ : ℝ) (hα₁ : IsGreatest {x | ∃ s, rowSum F s < 1 ∧ x = rowSum F s} α₁)
    (α₂ : ℝ) (hα₂ : IsLeast {x | ∃ i j, 0 < F i j ∧ x = F i j} α₂)
    (C : ℕ) :
    ∀ i, rowSum F i < 1 →
      rowSum (F ^ (C + 1)) i ≤ 1 - (1 - α₁) * α₂ ^ C ∧ 1 - (1 - α₁) * α₂ ^ C < 1 := by sorry

end SubSuperStoch.SubSpec
