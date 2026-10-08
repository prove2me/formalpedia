-- Prove2me | Theorems.Thm_VeinottNoDiscount_Improve_corollary_1
-- name    : VeinottNoDiscount.Improve.corollary_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:49:48.358996+00:00
-- url     : https://prove2.me/theorems/c17b2db9-db67-4076-8aee-38d7ac9a0c4c
-- title:
--   Corollary 1 — g ∈ G(f) ⇒ x(g) > x(f), or x(g) = x(f) and y(g) > y(f)
-- statement:
--   Let $f\in F$ and $g\in G(f)$. Then either
--   $$x(g)>x(f),\qquad\text{or}\qquad x(g)=x(f)\ \text{and}\ y(g)>y(f),$$
--   where $x$ is the gain, $y$ the bias, and $u>v$ means $u\ge v$ coordinatewise with $u\ne v$.
--
--   Each step of the policy improvement method therefore raises the pair (gain, bias) lexicographically.
-- source:
--   Veinott, On Finding Optimal Policies in Discrete Dynamic Programming with No Discounting, Ann. Math. Statist. 37(5):1284–1294 (1966), DOI 10.1214/aoms/1177699272, p. 1287, Corollary 1

import Mathlib
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_BlackwellDiscreteDP_NearOne_Model
import Definitions.Def_BlackwellDiscreteDP_NearOne_GainBias
import Definitions.Def_VeinottNoDiscount_Improve_Sets
open Filter Topology Matrix BlackwellDiscreteDP.NearOne

namespace VeinottNoDiscount.Improve

/-- **Corollary 1.** Suppose `f ε F` and `g ε G(f)`. Then either `x(g) > x(f)`, or
`x(g) = x(f)` and `y(g) > y(f)`.

Veinott, On Finding Optimal Policies in Discrete Dynamic Programming with No Discounting,
Ann. Math. Statist. 37(5):1284–1294 (1966), DOI 10.1214/aoms/1177699272, p. 1287, Corollary 1.

**Formalization Note.** `>` is `VecGt` (`≧` and `≠`, not coordinatewise strict). `x`, `y` are
Blackwell's closed forms `Q*(f)r(f)`, `H(f)r(f)`, the unique solutions of (2), (3). -/
theorem corollary_1 {St Act : Type*} [Fintype St] [DecidableEq St] [Nonempty St]
    [Fintype Act] [Nonempty Act] (M : Model St Act)
    (f g : St → Act) (hg : g ∈ GSet M f) :
    VecGt (M.x g) (M.x f) ∨ (M.x g = M.x f ∧ VecGt (M.y g) (M.y f)) := by sorry

end VeinottNoDiscount.Improve
