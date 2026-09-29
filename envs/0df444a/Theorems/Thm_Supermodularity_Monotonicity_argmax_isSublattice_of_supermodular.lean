-- Prove2me | Theorems.Thm_Supermodularity_Monotonicity_argmax_isSublattice_of_supermodular
-- name    : Supermodularity.Monotonicity.argmax_isSublattice_of_supermodular
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-18T05:27:18.190825+00:00
-- url     : https://prove2.me/theorems/3b8ca857-05be-44ab-a7fd-6351adda4547
-- title:
--   Theorem 2.7.1 - the set of maximizers of a supermodular function is a sublattice
-- statement:
--   Let $X$ be a lattice and let $f : X \to \mathbb{R}$ be **supermodular** on $X$ (see
--   `SupermodularOn`). Then
--
--   $$
--   \operatorname{argmax}_{x \in X} f(x) \;=\; \{x \in X : f(y) \le f(x) \text{ for all } y \in
--   X\}
--   $$
--
--   is a **sublattice** of $X$: it is closed under the pairwise join $\vee$ and meet $\wedge$
--   of $X$.
--
--   This is Theorem 2.7.1, the basic structural fact about maximizers of a supermodular
--   function: whenever $x'$ and $x''$ both maximize $f$, so do $x' \vee x''$ and $x' \wedge
--   x''$. It is the key step used repeatedly in Section 2.8 to show that the sets of optimal
--   solutions to a parameterized family of optimization problems are themselves sublattices,
--   which is what makes it meaningful to compare them with the induced set order.
--
--   **Formalization Note** $\operatorname{argmax}_{x \in X} f(x)$ is written as the set of $x$
--   that are an upper bound of $f$'s whole range, matching the book's convention that this set
--   may be empty (no assumption of compactness or upper semicontinuity is made here); the
--   claim is nonvacuous only when the maximum is actually attained. Sublattice membership is
--   expressed with Mathlib's `IsSublattice` predicate on `Set X`.
-- source:
--   Topkis, Supermodularity and Complementarity, Princeton University Press, 2011, p. 66, Theorem 2.7.1

import Mathlib
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn

namespace Supermodularity.Monotonicity

theorem argmax_isSublattice_of_supermodular {X : Type*} [Lattice X] (f : X → ℝ)
    (hf : SupermodularOn f Set.univ) :
    IsSublattice {x : X | ∀ y : X, f y ≤ f x} := by sorry

end Supermodularity.Monotonicity
