-- Prove2me | Theorems.Thm_ValuationSubring_exists_absoluteValue_isNonarchimedean_mem_iff_le_one_of_liesOverPrime
-- name    : ValuationSubring.exists_absoluteValue_isNonarchimedean_mem_iff_le_one_of_liesOverPrime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/960c6d51-ffd2-5cb3-86f1-6703664b625d
-- title:
--   Valuation subrings of ℚ̄ over p come from absolute values
-- statement:
--   Let $p$ be a prime number and let $A$ be a valuation subring of the algebraic closure $\overline{\mathbb{Q}}$ of $\mathbb{Q}$ which lies over $p$, meaning that the image of $p$ in $\overline{\mathbb{Q}}$ belongs to the set of non-units of $A$, i.e. $p$ lies in $A$ but is not invertible in $A$. The assertion is that there exists a real-valued absolute value $\mu$ on $\overline{\mathbb{Q}}$ (so $\mu$ is multiplicative, vanishes exactly at $0$ and satisfies the triangle inequality) with the following three properties: $\mu$ is non-archimedean, that is $\mu(a+b) \le \max(\mu(a),\mu(b))$ for all $a,b$; the value $\mu(p)$ at the image of $p$ satisfies $\mu(p) < 1$; and the closed unit ball of $\mu$ is exactly $A$, in the sense that for every $a \in \overline{\mathbb{Q}}$ one has $a \in A$ if and only if $\mu(a) \le 1$.
--
--   This is the statement that every valuation of $\overline{\mathbb{Q}}$ whose valuation ring contains $p$ as a non-unit has rank one, hence is induced by a non-archimedean real absolute value normalised so that $p$ is topologically nilpotent; it converts valuation-theoretic hypotheses into estimates with a real-valued $p$-adic-type absolute value. It is used throughout the analysis of integral models and charts on modular curves, where membership in a valuation subring must be compared with inequalities between real absolute values.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_absoluteValue_isNonarchimedean_mem_iff_le_one_of_liesOverPrime.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.exists_absoluteValue_isNonarchimedean_mem_iff_le_one_of_liesOverPrime
    {p : ℕ} (hp : p.Prime) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) :
    ∃ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ ∧
      μ (p : AlgebraicClosure ℚ) < 1 ∧ ∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1 := by sorry
