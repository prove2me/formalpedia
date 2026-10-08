-- Prove2me | Theorems.Thm_TensorNP_Rank_system30_consequences
-- name    : TensorNP.Rank.system30_consequences
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:07:54.003006+00:00
-- url     : https://prove2.me/theorems/c8d82f1f-df7c-472f-871b-602db738cc9f
-- title:
--   Proof of Lemma 8.1, p. 0:26 (sign corrected) — (30) implies 2c₂² − d₂² = 0 and c₁d₂d₃ + 2 = 0
-- statement:
--   Let $K$ be a field of characteristic zero, and let $a_1,\dots,d_3 \in K$ satisfy the eight equations (30) of Lemma 8.1. Then
--   $$
--   2c_2^2 - d_2^2 = 0 \qquad\text{and}\qquad c_1d_2d_3 + 2 = 0.
--   $$
--
--   These are the two polynomial consequences of (30) on which the proof of Lemma 8.1 rests: over $\mathbb Q$ the first forces $c_2 = d_2 = 0$, which contradicts the second.
--
--   **Formalization Note** The paper prints the second consequence as $c_1d_2d_3 - 2 = 0$. That is false: the real solution of (30) coming from $\bar{\mathbf z}\otimes\mathbf z\otimes\bar{\mathbf z} + \mathbf z\otimes\bar{\mathbf z}\otimes\mathbf z$ has $c_1 = 1$, $d_2 = -\sqrt2$, $d_3 = \sqrt2$, hence $c_1d_2d_3 = -2$. The statement uses the corrected sign; the paper's argument is unaffected. "Polynomial consequence" is read as: every solution in every field of characteristic zero (in particular in $\mathbb R$) satisfies the equation. Stated over $\mathbb Q$ alone the claim would hold vacuously, since by Lemma 8.1 (30) has no rational solution.
-- source:
--   Hillar & Lim, Most Tensor Problems Are NP-Hard, J. ACM 60(6) (2013), Art. 45 (final version, arXiv:0911.1393v5), p. 0:26, proof of Lemma 8.1; Appendix, p. 0:34, (41)

import Mathlib
import Definitions.Def_TensorNP_Rank_Construction

namespace TensorNP.Rank

theorem system30_consequences {K : Type*} [Field K] [CharZero K]
    (a₁ a₂ a₃ b₁ b₂ b₃ c₁ c₂ c₃ d₁ d₂ d₃ : K)
    (h : System30 a₁ a₂ a₃ b₁ b₂ b₃ c₁ c₂ c₃ d₁ d₂ d₃) :
    2 * c₂ ^ 2 - d₂ ^ 2 = 0 ∧ c₁ * d₂ * d₃ + 2 = 0 := by sorry

end TensorNP.Rank
