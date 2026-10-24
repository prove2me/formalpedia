-- Prove2me | Theorems.Thm_SaturatedNet_Uniqueness_proposition_1_i
-- name    : SaturatedNet.Uniqueness.proposition_1_i
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:37:36.31599+00:00
-- url     : https://prove2.me/theorems/5ce58ea3-37fd-4791-a58c-46838a159261
-- title:
--   Proposition 1 (i), p. 9 — the network equilibria form a complete lattice, with a minimal and a maximal equilibrium
-- statement:
--   Let $(P, w)$ be a network ($P \ge 0$ entrywise, $w \ge 0$) and $c \in \mathbb R^n$ any exogenous
--   flow, and let $\mathcal X$ be the set of network equilibria $x = S_0^w(P^\top x + c)$. Then
--   $\mathcal X$, ordered entrywise, is a complete lattice: every subset $S \subseteq \mathcal X$ has
--
--   $$\text{a least upper bound in } \mathcal X \quad\text{and}\quad \text{a greatest lower bound in } \mathcal X.$$
--
--   In particular there are a minimal network equilibrium $\underline x$ and a maximal network
--   equilibrium $\overline x$ in $\mathcal X$ (so $\mathcal X$ is nonempty).
--
--   The maximal equilibrium is the comparison point in the proof of Theorem 1, and the existence of an
--   equilibrium of a sub-network is what lets a solution on one class be completed to an equilibrium of
--   the whole network.
--
--   **Formalization Note.** The bounds are taken *within* $\mathcal X$: for every $S \subseteq \mathcal X$
--   the set of upper bounds of $S$ lying in $\mathcal X$ has a least element, and the set of lower bounds
--   lying in $\mathcal X$ has a greatest element. $\mathcal X$ is not claimed to be closed under the
--   entrywise supremum of $\mathbb R^n$. The recursion (13) mentioned in the preamble of the proposition
--   is not part of item (i) and is not formalized.
-- source:
--   Massai, Como & Fagnani, Equilibria and Systemic Risk in Saturated Networks, arXiv:1912.04815v2, p. 9, Proposition 1 (i)

import Mathlib
import Definitions.Def_SaturatedNet_Uniqueness_Model
open Matrix

namespace SaturatedNet.Uniqueness

theorem proposition_1_i {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hP : ∀ i j, 0 ≤ P i j) (w : n → ℝ) (hw : 0 ≤ w) (c : n → ℝ) :
    (∀ S ⊆ equilibria P w c,
      (∃ u, IsLeast (upperBounds S ∩ equilibria P w c) u) ∧
      (∃ l, IsGreatest (lowerBounds S ∩ equilibria P w c) l)) ∧
    (∃ xmin, IsLeast (equilibria P w c) xmin) ∧
    (∃ xmax, IsGreatest (equilibria P w c) xmax) := by sorry

end SaturatedNet.Uniqueness
