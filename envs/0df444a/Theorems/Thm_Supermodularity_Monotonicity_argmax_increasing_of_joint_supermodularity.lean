-- Prove2me | Theorems.Thm_Supermodularity_Monotonicity_argmax_increasing_of_joint_supermodularity
-- name    : Supermodularity.Monotonicity.argmax_increasing_of_joint_supermodularity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-18T05:29:02.459917+00:00
-- url     : https://prove2.me/theorems/2fc0ba05-fc8a-4bd3-8f70-c9a03ae7b613
-- title:
--   Theorem 2.8.2 - Topkis's monotonicity theorem for parameterized optimization
-- statement:
--   Let $X$ and $T$ be lattices, let $S$ be a **sublattice** of the product lattice $X \times
--   T$ (with $(x,t) \vee (x',t') = (x \vee x', t \vee t')$ and likewise for $\wedge$), and let
--   $f : X \times T \to \mathbb{R}$ be **supermodular** on $S$: $f(p) + f(q) \le f(p \vee q) +
--   f(p \wedge q)$ for all $p, q \in S$ (see `SupermodularOn`). For $t \in T$ write $S_t =
--   \{x \in X : (x,t) \in S\}$ for the section of $S$ at $t$. Then the correspondence
--
--   $$
--   t \;\longmapsto\; \operatorname{argmax}_{x \in S_t} f(x,t)
--   $$
--
--   is increasing in $t$, with respect to the induced set order $\sqsubseteq$ (see
--   `InducedSetOrder`), on the set of $t \in T$ for which $\operatorname{argmax}_{x \in S_t}
--   f(x,t)$ is nonempty.
--
--   This is Theorem 2.8.2, Topkis's own succinct headline theorem on monotone comparative
--   statics. Its hypothesis is deliberately joint: $f$ is supermodular in the *pair* $(x,t)$
--   on the sublattice $S$, not merely supermodular in $x$ for each fixed $t$ — the latter,
--   weaker property is the one used in Theorem 2.8.1. Joint supermodularity on a sublattice of
--   $X \times T$ automatically forces both the increasing-differences hypothesis and the
--   "$S_t$ increasing in $t$" hypothesis of Theorem 2.8.1, so Theorem 2.8.2's hypotheses,
--   while individually easier to verify in an application, are logically the stronger, more
--   special case.
--
--   **Formalization Note** As in Theorem 2.7.1 and Theorem 2.8.1, the argmax sets and the
--   conclusion are stated only for pairs $t \le t'$ at which both sets are nonempty, matching
--   the book's restriction to $\{t \in T : \operatorname{argmax}_{x \in S_t} f(x,t) \ne
--   \emptyset\}$. The corollary discussed in the book's prose immediately after this theorem
--   — specializing $X$, $T$ to $\mathbb{R}^n$, $\mathbb{R}^m$ and restating the hypotheses via
--   second partial derivatives of $f$ — is not itself a numbered theorem and is not
--   formalized here; the goal is proved for the general lattices $X$ and $T$, as the book
--   itself states it.
-- source:
--   Topkis, Supermodularity and Complementarity, Princeton University Press, 2011, p. 76-77, Theorem 2.8.2

import Mathlib
import Definitions.Def_Supermodularity_Lattices_InducedSetOrder
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn

namespace Supermodularity.Monotonicity

theorem argmax_increasing_of_joint_supermodularity {X T : Type*} [Lattice X] [Lattice T]
    (S : Set (X × T)) (hS : IsSublattice S) (f : X × T → ℝ)
    (hf : SupermodularOn f S) :
    ∀ ⦃t t' : T⦄, t ≤ t' →
      ({x : X | (x, t) ∈ S ∧ ∀ y : X, (y, t) ∈ S → f (y, t) ≤ f (x, t)}).Nonempty →
      ({x : X | (x, t') ∈ S ∧ ∀ y : X, (y, t') ∈ S → f (y, t') ≤ f (x, t')}).Nonempty →
      Supermodularity.Lattices.InducedSetOrder
        {x : X | (x, t) ∈ S ∧ ∀ y : X, (y, t) ∈ S → f (y, t) ≤ f (x, t)}
        {x : X | (x, t') ∈ S ∧ ∀ y : X, (y, t') ∈ S → f (y, t') ≤ f (x, t')} := by sorry

end Supermodularity.Monotonicity
