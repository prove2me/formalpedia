-- Prove2me | Theorems.Thm_SATotalCoeffLB_section_9_squares_nonneg_juntas
-- name    : SATotalCoeffLB.section_9_squares_nonneg_juntas
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:18:50.626977+00:00
-- url     : https://prove2.me/theorems/2e7b93b2-4f58-40c7-b6e5-f426196cf1d1
-- title:
--   Section 9 — squares of $k$-juntas are exactly the nonnegative $k$-juntas
-- statement:
--   In the Boolean quotient ring over a finite set of variables, an element $f$ is the square $f = h^2$ of a polynomial $h$ that depends on at most $k$ variables if and only if $f$ itself depends on at most $k$ variables and is nonnegative at every point of the cube.
--
--   With this, the identity of item 2 of Theorem 3 can be written as
--
--   $$
--   -1 = \sum_j h_j + \sum_{e \in \binom{[n]}{2}} C_e p_e + \sum_{e\in E} D_e q_e, \tag{25}
--   $$
--
--   where each $h_j$ is a nonnegative $k$-junta, which is the form to which the functional of Lemma 19 is applied.
--
--   Differences from the source:
--   - generalization: the variables $X, Y, T$ of the system → any finite set of variables $V$; reason: the statement does not depend on the variables; $V = X \sqcup Y \sqcup T$ is the page's case
--   - encoding: the Boolean quotient ring $\mathbb R[\text{variables}]/\langle y^2-1\rangle$ → real functions on bit vectors, variable $v$ evaluating to $(-1)^{x_v}$ (`CubeFn`); reason: for finitely many variables evaluation on the $\pm1$ cube is a ring isomorphism; same identities
-- source:
--   Chen–Jin, Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for Sherali–Adams, STOC 2027 submission (manuscript sha256 da19ece6…9d9178), Section 9, p.50 (before Eq. (25))

import Mathlib
import Definitions.Def_SATotalCoeffLB_DependsOnAtMost

namespace SATotalCoeffLB

/-- **Section 9, squares of `k`-juntas are the nonnegative `k`-juntas**, p.50 of Chen–Jin, *Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for
Sherali–Adams*, STOC 2027 submission manuscript
(sha256 da19ece6898e20b159d01408327de710d69219772cc1f088c80301a6679d9178).

In the Boolean quotient ring, an element is the square of a polynomial depending on at most `k`
variables if and only if it depends on at most `k` variables and is nonnegative at every point of
the cube. (This rewrites the identity of Theorem 3, item 2, as Eq. (25).)

**Formalization Note** Stated for an arbitrary finite set of variables `V`. -/
theorem section_9_squares_nonneg_juntas {V : Type*} [Fintype V] (k : ℕ) (f : CubeFn V) :
    (∃ h : CubeFn V, DependsOnAtMost k h ∧ f = h ^ 2) ↔
      (DependsOnAtMost k f ∧ ∀ x, 0 ≤ f x) := by sorry

end SATotalCoeffLB
