-- Prove2me | Theorems.Thm_SubSuperStoch_AsyncTrack_theorem_2_4_1
-- name    : SubSuperStoch.AsyncTrack.theorem_2_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:43:15.620545+00:00
-- url     : https://prove2.me/theorems/691e9d57-6f6b-4bbd-b173-ad2024a6e1c7
-- title:
--   Theorem 2.4 1), p. 7 — a product of sub-stochastic matrices is sub-stochastic
-- statement:
--   Let $F_1,F_2,\dots,F_q\in\mathbb R^{n\times n}$ be sub-stochastic matrices: each has nonnegative entries and all its row sums $\Lambda_i[F_s]=\sum_j[F_s]_{ij}$ are at most $1$. Then the ordered product
--   $$\prod_{s=1}^q F_s=F_qF_{q-1}\cdots F_1$$
--   is again a sub-stochastic matrix.
--
--   This closure property lets the paper treat a run of consecutive transition matrices of a positive switched system as a single sub-stochastic matrix; it is used in part 2) of Theorem 2.4 and in Lemma 3.2.
--
--   **Formalization Note** The matrices are the values $F(1),\dots,F(q)$ of a sequence `F : ℕ → Matrix (Fin n) (Fin n) ℝ`; only these are assumed sub-stochastic, and the product is `prodFrom F 1 q`. For $q=0$ the product is the identity matrix, which is sub-stochastic.
-- source:
--   Shi, Zheng, Shao, Cheng, arXiv:2004.01867v2, p. 7, Theorem 2.4 1)

import Mathlib
import Definitions.Def_SubSuperStoch_AsyncTrack_Matrix

namespace SubSuperStoch.AsyncTrack

/-- Theorem 2.4 1) (p. 7): for sub-stochastic matrices `F₁, …, F_q`, the product
`∏_{s=1}^q F_s = F_q ⋯ F_1` is sub-stochastic. -/
theorem theorem_2_4_1 {n : ℕ} (F : ℕ → Matrix (Fin n) (Fin n) ℝ) (q : ℕ)
    (hF : ∀ s, 1 ≤ s → s ≤ q → IsSubStochastic (F s)) :
    IsSubStochastic (prodFrom F 1 q) := by sorry

end SubSuperStoch.AsyncTrack
