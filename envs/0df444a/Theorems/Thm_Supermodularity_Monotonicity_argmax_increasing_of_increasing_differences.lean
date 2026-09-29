-- Prove2me | Theorems.Thm_Supermodularity_Monotonicity_argmax_increasing_of_increasing_differences
-- name    : Supermodularity.Monotonicity.argmax_increasing_of_increasing_differences
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-18T05:27:51.893932+00:00
-- url     : https://prove2.me/theorems/01c7b4dd-d978-4f39-9975-53b412a0c880
-- title:
--   Theorem 2.8.1 - increasing optimal solutions from supermodularity and increasing differences
-- statement:
--   Let $X$ be a lattice and $T$ a partially ordered set. Suppose that $S_t \subseteq X$ is
--   given for each $t \in T$, that $t \mapsto S_t$ is **increasing** in $t$ on $T$ with respect
--   to the induced set order $\sqsubseteq$ (see `InducedSetOrder`), that $f(x,t)$ is
--   **supermodular** in $x$ on $X$ for each fixed $t \in T$, and that $f(x,t)$ has
--   **increasing differences** in $(x,t)$ on $X \times T$ (see `IncreasingDifferencesOn`).
--   Then the correspondence
--
--   $$
--   t \;\longmapsto\; \operatorname{argmax}_{x \in S_t} f(x,t)
--   $$
--
--   is increasing in $t$, with respect to $\sqsubseteq$, on the set of $t \in T$ for which
--   $\operatorname{argmax}_{x \in S_t} f(x,t)$ is nonempty.
--
--   This is Theorem 2.8.1, the book's central sufficient condition for **monotone comparative
--   statics**: increasing differences between the decision variable and the parameter, plus
--   supermodularity of the objective in the decision variable, forces the optimal-solution
--   correspondence to move up (in the induced set order) as the parameter increases. It
--   follows from Lemma 2.8.1 by using increasing differences and supermodularity in $x$ to
--   verify Lemma 2.8.1's joint inequality; the consequence of Theorem 2.7.1 that each
--   $\operatorname{argmax}_{x\in S_t}f(x,t)$ is a sublattice of $X$ underlies why comparing
--   these sets with $\sqsubseteq$ is meaningful.
--
--   **Formalization Note** "$S_t$ is increasing in $t$" is Topkis's induced set order on
--   subsets of $X$, imported from chunk `01-lattices`. The conclusion is stated pairwise for
--   $t \le t'$ with both argmax sets assumed nonempty, matching the book's restriction of the
--   claim to $\{t \in T : \operatorname{argmax}_{x\in S_t}f(x,t) \ne \emptyset\}$: the induced
--   set order holds vacuously whenever either side is empty, so both nonemptiness hypotheses
--   are needed to recover the book's actual claim rather than a vacuously true one.
-- source:
--   Topkis, Supermodularity and Complementarity, Princeton University Press, 2011, p. 76, Theorem 2.8.1

import Mathlib
import Definitions.Def_Supermodularity_Lattices_InducedSetOrder
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn
import Definitions.Def_Supermodularity_Monotonicity_IncreasingDifferencesOn

namespace Supermodularity.Monotonicity

theorem argmax_increasing_of_increasing_differences {X T : Type*} [Lattice X] [PartialOrder T]
    (S : T → Set X) (f : X → T → ℝ)
    (hS : ∀ ⦃t t' : T⦄, t ≤ t' → Supermodularity.Lattices.InducedSetOrder (S t) (S t'))
    (hsuper : ∀ t : T, SupermodularOn (fun x => f x t) Set.univ)
    (hdiff : IncreasingDifferencesOn f Set.univ) :
    ∀ ⦃t t' : T⦄, t ≤ t' →
      ({x : X | x ∈ S t ∧ ∀ y ∈ S t, f y t ≤ f x t}).Nonempty →
      ({x : X | x ∈ S t' ∧ ∀ y ∈ S t', f y t' ≤ f x t'}).Nonempty →
      Supermodularity.Lattices.InducedSetOrder
        {x : X | x ∈ S t ∧ ∀ y ∈ S t, f y t ≤ f x t}
        {x : X | x ∈ S t' ∧ ∀ y ∈ S t', f y t' ≤ f x t'} := by sorry

end Supermodularity.Monotonicity
