-- Prove2me | Theorems.Thm_RudinSquares_recursion
-- name    : RudinSquares.recursion
-- status  : Open
-- author  : @LG
-- created : 2026-11-18T18:23:44.94561+00:00
-- url     : https://prove2.me/theorems/c91519ba-b6a7-4c6e-b83f-3d55f212b975
-- title:
--   Section 6 — the recursion $Q(N)\le Q(N+1)\le Q(N)+1$ and the $z_I$ criterion
-- statement:
--   The recursive engine of Section 6. For every $N\ge0$,
--   $$Q(N)\le Q(N+1)\le Q(N)+1,$$
--   and the value does not increase exactly when every $(Q(N)+1)$-element index set inside $\{0,\dots,N\}$ supports no progression:
--   $$Q(N+1)=Q(N)\quad\Longleftrightarrow\quad \bigl(\forall I\subseteq\{0,\dots,N\},\ \#I=Q(N)+1\ \Rightarrow\ z_I=0\bigr).$$
--   Thus, knowing $Q(N)$, one computes $Q(N+1)$ by determining $z_I$ for all $(Q(N)+1)$-subsets $I$ of $\{0,\dots,N\}$: if all vanish then $Q(N+1)=Q(N)$, otherwise $Q(N+1)=Q(N)+1$. This reduces Theorem 1 to the finite collection of $z_I$ computations carried out in the paper.
-- source:
--   E. González-Jiménez and X. Xarles, 'On a conjecture of Rudin on squares in arithmetic progressions', LMS J. Comput. Math. 17(1) (2014) 58–76, doi:10.1112/S1461157013000259, §6 (Consequences and comments), p. 73.

import Mathlib
import Definitions.Def_RudinSquares_Defs

namespace RudinSquares
theorem recursion (N : ℕ) :
    Q N ≤ Q (N + 1) ∧ Q (N + 1) ≤ Q N + 1 ∧
    (Q (N + 1) = Q N ↔
      ∀ I : Finset ℤ, I ⊆ Finset.Icc (0 : ℤ) (N : ℤ) → I.card = Q N + 1 → z I = 0) := by sorry
end RudinSquares
