-- Prove2me | Theorems.Thm_TensorNP_Rank_lemma_8_1
-- name    : TensorNP.Rank.lemma_8_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:07:48.116718+00:00
-- url     : https://prove2.me/theorems/8e4d3e13-a158-44ac-8335-3c4009bcd0a3
-- title:
--   Lemma 8.1, p. 0:26 — the system (30) of 8 equations in 12 unknowns has no rational solution
-- statement:
--   The system of eight equations in the twelve unknowns $a_1,a_2,a_3,b_1,b_2,b_3,c_1,c_2,c_3,d_1,d_2,d_3$
--   $$
--   \begin{aligned}
--   &a_1a_2a_3 + c_1c_2c_3 = 2, && a_1a_3b_2 + c_1c_3d_2 = 0, && a_2a_3b_1 + c_2c_3d_1 = 0, && a_3b_1b_2 + c_3d_1d_2 = -4,\\
--   &a_1a_2b_3 + c_1c_2d_3 = 0, && a_1b_2b_3 + c_1d_2d_3 = -4, && a_2b_1b_3 + c_2d_3d_1 = 4, && b_1b_2b_3 + d_1d_2d_3 = 0
--   \end{aligned}
--   \tag{30}
--   $$
--   has no solution in rational numbers.
--
--   It has real solutions (for instance the one coming from $\bar{\mathbf z}\otimes\mathbf z\otimes\bar{\mathbf z} + \mathbf z\otimes\bar{\mathbf z}\otimes\mathbf z$ with $\mathbf z = [1,\sqrt2]^\top$), so the obstruction is arithmetic, not real-algebraic. This lemma is the lower half of Theorem 1.14.
-- source:
--   Hillar & Lim, Most Tensor Problems Are NP-Hard, J. ACM 60(6) (2013), Art. 45 (final version, arXiv:0911.1393v5), p. 0:26, Lemma 8.1

import Mathlib
import Definitions.Def_TensorNP_Rank_Construction

namespace TensorNP.Rank

theorem lemma_8_1 :
    ¬ ∃ a₁ a₂ a₃ b₁ b₂ b₃ c₁ c₂ c₃ d₁ d₂ d₃ : ℚ,
      System30 a₁ a₂ a₃ b₁ b₂ b₃ c₁ c₂ c₃ d₁ d₂ d₃ := by sorry

end TensorNP.Rank
