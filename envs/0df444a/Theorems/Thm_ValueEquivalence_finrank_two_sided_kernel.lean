-- Prove2me | Theorems.Thm_ValueEquivalence_finrank_two_sided_kernel
-- name    : ValueEquivalence.finrank_two_sided_kernel
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-23T17:51:51.152501+00:00
-- url     : https://prove2.me/theorems/a993ecc4-3a57-4122-a0d4-34ef8244ce7a
-- title:
--   Lemma 1: the dimension of {B : ABC = 0}
-- statement:
--   Let $\boldsymbol A\in\mathbb R^{k\times n}$ and $\boldsymbol C\in\mathbb R^{m\times\ell}$ be arbitrary real matrices, and let
--
--   $$\mathcal B=\{\boldsymbol B\in\mathbb R^{n\times m}:\boldsymbol A\boldsymbol B\boldsymbol C=\boldsymbol 0\},$$
--
--   a linear subspace of $\mathbb R^{n\times m}$. Then
--
--   $$\dim\mathcal B=nm-\operatorname{rank}(\boldsymbol A)\cdot\operatorname{rank}(\boldsymbol C).$$
--
--   This is the linear-algebra step behind the dimension bound of Proposition 2.
--
--   **Formalization Note** The equation is stated in the integers, so that the right-hand side is not truncated.
-- source:
--   Grimm, Barreto, Singh and Silver, The Value Equivalence Principle for Model-Based Reinforcement Learning, arXiv:2011.03506v1 (2020), Appendix A.1.1, Lemma 1, eq. (8), p. 14

import Mathlib
import Definitions.Def_ValueEquivalence_Basic

open Filter Topology

namespace ValueEquivalence

theorem finrank_two_sided_kernel {k n m l : ℕ} (A : Matrix (Fin k) (Fin n) ℝ)
    (C : Matrix (Fin m) (Fin l) ℝ) :
    (Module.finrank ℝ (twoSidedKernel A C) : ℤ) = (n : ℤ) * m - (A.rank : ℤ) * C.rank := by sorry

end ValueEquivalence
