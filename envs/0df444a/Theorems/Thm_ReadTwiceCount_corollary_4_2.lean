-- Prove2me | Theorems.Thm_ReadTwiceCount_corollary_4_2
-- name    : ReadTwiceCount.corollary_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:40:21.979257+00:00
-- url     : https://prove2.me/theorems/da71fbae-ef28-49f1-ae3c-d3e9f6f8368c
-- title:
--   Corollary 4.2 — $\sum_{u\text{ in the frontier}}\sqrt{D_u}\le1$
-- statement:
--   **Corollary 4.2.** At any finite input to a partial computation tree,
--   $$\sum_{u\text{ in the frontier}}\sqrt{D_u}\le1 .$$
--
--   Stated for every descriptor tree whose node descriptors are nonsingular and whose constants are at least $1$, at frontier inputs $x_u\ge1$; $D_u$ is the product of the absolute local partial derivatives along the path to $u$. In particular every path derivative is at most one. This is the budget (21) that allocates accuracy to the boundary calls.
--
--   Differences from the source:
--   - generalization: a partial computation tree → every descriptor tree with nonsingular node descriptors and constants at least $1$; reason: a partial computation tree of a positive dangling query is such a tree (its node descriptors are nonsingular and its exact constants are coordinates, at least $1$), and the paper's proof uses only Lemma 4.1 at each node
--   - reading: $D_u$, "the absolute derivative of the root with respect to that frontier input … a product along its path" → the product of the absolute local partial derivatives along the path; reason: the paper's own description (p.5); by the chain rule it is the absolute derivative of the root
-- source:
--   He, A Deterministic Approximation Scheme for Counting Read-Twice CNF Assignments, STOC 2027 submission (manuscript sha256 7a2a9dcd…), Corollary 4.2, display (10), p.6; the definition of $D_u$, p.5

import Mathlib
import Definitions.Def_ReadTwiceCount_DTree

namespace ReadTwiceCount

/-- **Corollary 4.2** (He, *A Deterministic Approximation Scheme for Counting Read-Twice CNF Assignments*, STOC 2027
submission (manuscript sha256 7a2a9dcd…), Corollary 4.2, p.6): "At any finite
input to a partial computation tree, Σ_{u in the frontier} √D_u ≤ 1." (10)

**Formalization Note** Stated for every descriptor tree whose node descriptors are nonsingular and
whose constants are at least 1, at frontier inputs at least 1; a partial computation tree of a
positive dangling state is such a tree. `D_u` is the product of the absolute local partial derivatives
along the path to `u` (p.5). -/
theorem corollary_4_2 (T : DTree) (hT : T.WellFormed) (x : List ℕ → ℝ)
    (hx : ∀ u ∈ T.leaves, 1 ≤ x u) :
    ∑ u ∈ T.leaves, Real.sqrt (T.pathDeriv x u) ≤ 1 := by sorry

end ReadTwiceCount
