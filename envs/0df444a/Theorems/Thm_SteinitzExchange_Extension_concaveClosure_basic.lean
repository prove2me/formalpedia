-- Prove2me | Theorems.Thm_SteinitzExchange_Extension_concaveClosure_basic
-- name    : SteinitzExchange.Extension.concaveClosure_basic
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:44:13.938823+00:00
-- url     : https://prove2.me/theorems/6d5356b7-898f-40d5-9129-26e70f1ec746
-- title:
--   Lemma 4.1 — the concave closure dominates $g$ on $B$, has the same maximum, and its maximizers are $\overline{\operatorname{argmax}(g)}$
-- statement:
--   Let $B\subseteq\mathbb Z^V$ be a nonempty finite set, $g:B\to\mathbb R$ any function, and $\hat g$ its concave closure, regarded as a function on $\overline B$. Then:
--
--   1. $\hat g(x)\ge g(x)$ for every $x\in B$;
--   2. $\max\{\hat g(b)\mid b\in\overline B\}=\max\{g(x)\mid x\in B\}$, the maximum on the left being attained;
--   3. $\operatorname{argmax}(\hat g)=\overline{\operatorname{argmax}(g)}$, where $\operatorname{argmax}(\hat g)=\{b\in\overline B\mid\hat g(b)\ge\hat g(c)\ \forall c\in\overline B\}$ and the right side is the convex hull of $\operatorname{argmax}(g)\subseteq B$.
--
--   No exchange property is assumed. The lemma transfers maximization questions about $g$ on the lattice points to the concave function $\hat g$ on the polytope $\overline B$.
--
--   **Formalization Note.** Part (2) is stated as: some $b\in\overline B$ has $\hat g(b)=\max_B g$, and $\hat g(b)\le\max_B g$ for all $b\in\overline B$. All three parts evaluate $\hat g$ only on $\overline B$ (see the definition of `concaveClosure`).
-- source:
--   Murota, Convexity and Steinitz's Exchange Property, Adv. Math. 124 (1996), p. 285, Lemma 4.1

import Mathlib
import Definitions.Def_SteinitzExchange_Extension_IntegralBaseSet
import Definitions.Def_SteinitzExchange_Extension_Exchange
import Definitions.Def_SteinitzExchange_Extension_ConcaveClosure

namespace SteinitzExchange.Extension

/-- Murota 1996, p. 285, Lemma 4.1, for any `g : B → ℝ` on a nonempty finite `B ⊆ ℤ^V`:
(1) `ĝ(x) ≥ g(x)` for `x ∈ B`;
(2) `max{ĝ(b) | b ∈ B̄} = max{g(x) | x ∈ B}` (the left maximum is attained);
(3) `argmax(ĝ) = conv(argmax(g))`, the argmax of `ĝ` taken over `B̄`. -/
theorem concaveClosure_basic {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : B.Nonempty) (g : (V → ℤ) → ℝ) :
    (∀ x ∈ B, g x ≤ concaveClosure B g (toReal x)) ∧
    ((∃ b ∈ hull B, concaveClosure B g b = B.sup' hB g) ∧
      ∀ b ∈ hull B, concaveClosure B g b ≤ B.sup' hB g) ∧
    argmaxOn (hull B) (concaveClosure B g) = hull (argmaxB B g) := by sorry

end SteinitzExchange.Extension
