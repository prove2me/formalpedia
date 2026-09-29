-- Prove2me | Theorems.Thm_Supermodularity_Lattices_increasing_correspondence_fixed_point
-- name    : Supermodularity.Lattices.increasing_correspondence_fixed_point
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-18T05:25:03.016163+00:00
-- url     : https://prove2.me/theorems/f2e385ae-c8ff-4da2-afd8-e1aad0eec5fd
-- title:
--   Theorem 2.5.1 - Zhou's fixed point theorem for an increasing correspondence
-- statement:
--   Let $X$ be a nonempty **complete lattice** and let $Y : X \to \mathcal{P}(X)$ be an
--   **increasing correspondence** from $X$ into $X$: $x \preceq x'$ implies
--   $Y(x) \sqsubseteq Y(x')$ in the induced set ordering. Suppose $Y(x)$ is a
--   **nonempty subcomplete** sublattice of $X$ for every $x \in X$. A point $x \in X$ is a **fixed point** of $Y$ if $x \in Y(x)$.
--
--   This is Theorem 2.5.1, Zhou's [1994] extension of Tarski's [1955] fixed point
--   theorem from single-valued increasing functions to set-valued increasing
--   correspondences.
--
--   (a) The set of fixed points of $Y$ is nonempty. Moreover,
--
--   $$
--   x^\* \;=\; \sup\nolimits_X\{\,x \in X : Y(x) \cap [x, \infty) \neq \emptyset\,\}
--   $$
--
--   is the **greatest** fixed point of $Y$, and
--
--   $$
--   x_\* \;=\; \inf\nolimits_X\{\,x \in X : Y(x) \cap (-\infty, x] \neq \emptyset\,\}
--   $$
--
--   is the **least** fixed point of $Y$, where $[x,\infty) = \{y \in X : x \preceq y\}$
--   and $(-\infty, x] = \{y \in X : y \preceq x\}$.
--
--   (b) The set of fixed points of $Y$, equipped with the order it inherits from $X$, is
--   itself a nonempty complete lattice: every nonempty subset of fixed points has a
--   least upper bound and a greatest lower bound *among the fixed points*. (This is
--   genuinely a separate fact from the fixed points forming a sublattice of $X$ — they
--   need not: two fixed points can have a join or a meet, computed in $X$, that fails to
--   be a fixed point.)
--
--   **Formalization Note** Nonemptiness of each $Y(x)$ is an explicit hypothesis (`hne`),
--   since the `Subcomplete` predicate is vacuously true of the empty set. "Nonempty complete lattice" needs no separate hypothesis:
--   Lean's `CompleteLattice` typeclass already forces the carrier type to be nonempty
--   (via its top element). Part (b) is stated as: every nonempty set of fixed points has
--   both an upper bound and a lower bound that are themselves least/greatest among the
--   fixed points (`IsLUB`/`IsGLB` computed on the subtype of fixed points) — deliberately
--   *not* as membership of the ambient supremum/infimum in the fixed-point set, since
--   that stronger claim is false in general (Topkis's Example 2.5.1).
-- source:
--   Topkis, Supermodularity and Complementarity, Princeton University Press, 2011, p. 39, Theorem 2.5.1

import Mathlib
import Definitions.Def_Supermodularity_Lattices_InducedSetOrder
import Definitions.Def_Supermodularity_Lattices_Subcomplete

namespace Supermodularity.Lattices

theorem increasing_correspondence_fixed_point {X : Type*} [CompleteLattice X] (Y : X → Set X)
    (hinc : ∀ ⦃x x' : X⦄, x ≤ x' → InducedSetOrder (Y x) (Y x'))
    (hne : ∀ x : X, (Y x).Nonempty) (hsub : ∀ x : X, Subcomplete (Y x)) :
    {x : X | x ∈ Y x}.Nonempty ∧
      IsGreatest {x : X | x ∈ Y x} (sSup {x : X | (Y x ∩ Set.Ici x).Nonempty}) ∧
      IsLeast {x : X | x ∈ Y x} (sInf {x : X | (Y x ∩ Set.Iic x).Nonempty}) ∧
      (∀ F : Set {x : X // x ∈ Y x}, F.Nonempty → ∃ m, IsLUB F m) ∧
      (∀ F : Set {x : X // x ∈ Y x}, F.Nonempty → ∃ m, IsGLB F m) := by sorry

end Supermodularity.Lattices
