-- Prove2me | Theorems.Thm_Supermodularity_Lattices_inter_increasing_of_forall_increasing
-- name    : Supermodularity.Lattices.inter_increasing_of_forall_increasing
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-18T05:24:11.298444+00:00
-- url     : https://prove2.me/theorems/d9af8b20-8d17-4af8-9a5a-0c4c8e720911
-- title:
--   Theorem 2.4.2 - the intersection of increasing correspondences is increasing
-- statement:
--   Let $X$ be a lattice, $T$ a partially ordered set, and $A$ an index set. Suppose
--   that for each $\alpha \in A$, the correspondence $t \mapsto S_\alpha(t) \subseteq X$
--   is **increasing** in $t$ on $T$ with respect to the induced set ordering $\sqsubseteq$
--   (that is, $t \preceq t'$ in $T$ implies $S_\alpha(t) \sqsubseteq S_\alpha(t')$), and
--   that $\bigcap_{\alpha \in A} S_\alpha(t)$ is nonempty for every $t \in T$. Then the
--   correspondence
--
--   $$
--   t \mapsto \bigcap_{\alpha \in A} S_\alpha(t)
--   $$
--
--   is itself increasing in $t$ on $T$ with respect to $\sqsubseteq$.
--
--   This is Theorem 2.4.2: the induced set ordering is preserved under taking
--   intersections of increasing correspondences, provided the intersection stays
--   nonempty. It underlies, for instance, the fact that the correspondence
--   $x \mapsto Y(x) \cap [\,\sup X'', \infty)$ appearing in the proof of Theorem 2.5.1
--   is increasing whenever $Y$ is.
--
--   **Formalization Note** "Partially ordered set" is formalized as `PartialOrder T`,
--   matching the book's convention throughout Chapter 2. No hypothesis is placed on the
--   index set $A$ beyond being a type; $A$ may be infinite.
-- source:
--   Topkis, Supermodularity and Complementarity, Princeton University Press, 2011, p. 34, Theorem 2.4.2

import Mathlib
import Definitions.Def_Supermodularity_Lattices_InducedSetOrder

namespace Supermodularity.Lattices

theorem inter_increasing_of_forall_increasing {X T A : Type*} [Lattice X] [PartialOrder T]
    (S : A → T → Set X)
    (hinc : ∀ α : A, ∀ ⦃t t' : T⦄, t ≤ t' → InducedSetOrder (S α t) (S α t'))
    (hne : ∀ t : T, (⋂ α, S α t).Nonempty) :
    ∀ ⦃t t' : T⦄, t ≤ t' → InducedSetOrder (⋂ α, S α t) (⋂ α, S α t') := by sorry

end Supermodularity.Lattices
