-- Prove2me | Theorems.Thm_Supermodularity_Lattices_parametrized_fixed_point_monotone
-- name    : Supermodularity.Lattices.parametrized_fixed_point_monotone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-18T05:25:40.086586+00:00
-- url     : https://prove2.me/theorems/f4999b4b-e2ec-4238-8558-843a67597f3a
-- title:
--   Theorem 2.5.2 - Zhou's fixed point theorem with a parameter
-- statement:
--   Let $X$ be a nonempty complete lattice and $T$ a partially ordered set. Suppose
--   $Y(x,t) \subseteq X$ is a nonempty subcomplete sublattice of $X$ for every
--   $(x,t) \in X \times T$, and the correspondence $Y$ is **increasing** on $X \times T$
--   with respect to the induced set ordering $\sqsubseteq$ on its range: whenever
--   $x \preceq x'$ in $X$ and $t \preceq t'$ in $T$, $Y(x,t) \sqsubseteq Y(x',t')$.
--
--   This is Theorem 2.5.2, Zhou's [1994] fixed point theorem with a parameter,
--   generalizing Milgrom and Roberts [1994].
--
--   (a) For each $t \in T$, the correspondence $x \mapsto Y(x,t)$ has a greatest fixed
--   point $g(t)$ and a least fixed point $l(t)$ (Theorem 2.5.1 applied at the fixed
--   parameter $t$).
--
--   (b) Both $g$ and $l$ are **increasing** (monotone) functions of $t$ on $T$.
--
--   (c) If, in addition, $\sup_X Y(x', t') \prec \inf_X Y(x', t'')$ for every $x' \in X$
--   and every $t' \prec t''$ in $T$ (a strict-separation condition on the ranges of $Y$
--   across parameter values), then both $g$ and $l$ are **strictly** increasing on $T$.
--
--   **Formalization Note** Parts (a) and (b) are packaged together as the existence of
--   two monotone choice functions $g, l : T \to X$ realizing the greatest and least
--   fixed point at each $t$; this is the standard way to render "there exists a greatest
--   fixed point, and it is increasing in $t$" in dependent type theory, since the
--   greatest fixed point at each $t$ is unique (by antisymmetry) and so $g$, $l$ are
--   genuine functions of $t$, not merely selections. Part (c)'s conclusion is expressed
--   as an implication from the extra separation hypothesis to strict monotonicity of the
--   very same $g$ and $l$ produced in (a)–(b).
-- source:
--   Topkis, Supermodularity and Complementarity, Princeton University Press, 2011, p. 41, Theorem 2.5.2

import Mathlib
import Definitions.Def_Supermodularity_Lattices_InducedSetOrder
import Definitions.Def_Supermodularity_Lattices_Subcomplete

namespace Supermodularity.Lattices

theorem parametrized_fixed_point_monotone {X : Type*} [CompleteLattice X] {T : Type*}
    [PartialOrder T] (Y : X → T → Set X)
    (hne : ∀ x : X, ∀ t : T, (Y x t).Nonempty) (hsub : ∀ x : X, ∀ t : T, Subcomplete (Y x t))
    (hinc : ∀ ⦃x x' : X⦄, ∀ ⦃t t' : T⦄, x ≤ x' → t ≤ t' → InducedSetOrder (Y x t) (Y x' t')) :
    ∃ g l : T → X,
      Monotone g ∧ Monotone l ∧
        (∀ t : T, IsGreatest {x : X | x ∈ Y x t} (g t)) ∧
        (∀ t : T, IsLeast {x : X | x ∈ Y x t} (l t)) ∧
        ((∀ x' : X, ∀ ⦃t' t'' : T⦄, t' < t'' → sSup (Y x' t') < sInf (Y x' t'')) →
          StrictMono g ∧ StrictMono l) := by sorry

end Supermodularity.Lattices
