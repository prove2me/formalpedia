-- Prove2me | Theorems.Thm_RegretMatching_Approach_exists_invariant_vector
-- name    : RegretMatching.Approach.exists_invariant_vector
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T00:02:46.598899+00:00
-- url     : https://prove2.me/theorems/53044b6b-9e9a-4428-b410-4ffef5ad61a9
-- title:
--   §3, proof of THEOREM A, p. 1137, (3.5) — a nonnegative zero-diagonal matrix has an invariant probability vector
-- statement:
--   Let $A$ be a finite nonempty set and $L=\{(j,k)\in A\times A: j\ne k\}$. Let $\lambda\in\mathbb R^L$ have nonnegative coordinates, and let $\Lambda_\lambda$ be the $A\times A$ matrix with entries $\lambda(j,k)$ for $j\ne k$ and $0$ for $j=k$. Then there is a probability vector $q\in\Delta(A)$ which is invariant for $\Lambda_\lambda$ in the sense of (3.5):
--   $$\sum_{k\in A}q(k)\,\Lambda_\lambda(k,j)=q(j)\sum_{k\in A}\Lambda_\lambda(j,k)\qquad\text{for every }j\in A .$$
--
--   In the proof of Theorem A this supplies the mixed strategy $q_\lambda$ that meets Blackwell's condition for the nonpositive orthant. Taking $\lambda$ to be the vector of regrets $(R^i_t(j,k))_{j\neq k}$ it also shows that (3.1) has a solution in $\Delta(S^i)$ at every history, so the hypothesis of Theorem A can always be met.
--
--   **Formalization Note.** The statement is for an arbitrary finite nonempty set $A$ (in use $A=S^i$). Nonemptiness is needed for $\Delta(A)$ to be nonempty.
-- source:
--   Hart and Mas-Colell, A simple adaptive procedure leading to correlated equilibrium, Econometrica 68 (2000), p. 1137, proof of THEOREM A, (3.5); also p. 1133 ('such a vector always exists')

import Mathlib
import Definitions.Def_RegretMatching_Approach_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace RegretMatching.Approach

theorem exists_invariant_vector
    {A : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    (lam : OffDiag A → ℝ) (hlam : ∀ l, 0 ≤ lam l) :
    ∃ q ∈ stdSimplex ℝ A, ∀ j : A,
      ∑ k : A, q k * lamMat lam k j = q j * ∑ k : A, lamMat lam j k := by sorry

end RegretMatching.Approach
