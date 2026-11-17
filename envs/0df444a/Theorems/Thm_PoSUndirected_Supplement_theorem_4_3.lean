-- Prove2me | Theorems.Thm_PoSUndirected_Supplement_theorem_4_3
-- name    : PoSUndirected.Supplement.theorem_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T00:33:28.950438+00:00
-- url     : https://prove2.me/theorems/dea52476-4387-42b0-83c5-24d6eefd229b
-- title:
--   Theorem 4.3 — sharp owner bound $1348/715$
-- statement:
--   Suppose a finite loopless host has positive real edge costs, maximum physical block rank at most three, and one endpoint owner for each edge of an arbitrary nonempty subset $E_{\mathrm{own}}\subseteq E$. Then
--   $$
--   \mathrm{PoS}<\frac{1348}{715}.
--   $$
--   The supremum over this entire class is exactly $1348/715$: every finite instance obeys the strict bound and instances approach the constant arbitrarily closely. For positive rational costs encoded in binary, one uniform polynomial-time algorithm computes a cheapest weak equilibrium.
--
--   Differences from the source:
--   - encoding: the supremum over all finite owner games → a strict upper clause over `Fin n` presentations and an $\varepsilon$-approximation lower clause; reason: every finite instance is isomorphic to a `Fin n` presentation and the two clauses are the definition of this unattained supremum
--   - encoding: polynomial-time computation for binary rational costs → a Mathlib multi-tape Turing machine on an explicit binary incidence, owned-set and rational-cost encoding, returning the profile incidence matrix; reason: standard exact bit-complexity reading of the paper's algorithmic convention
-- source:
--   Tsoufis, The Price of Stability in Undirected Network Design: Lower Bounds and Structural Guarantees (preprint, sha256 c095d811fa04b471d74ba4fdab8fb89ccb3d34079d3bf07384f46ac57144866c), Theorem 4.3, p.8 (PDF p.10); Proposition B.10, p.54 (PDF p.56)

import Mathlib
import Definitions.Def_PoSUndirected_Supplement_OwnerRankClassSupremum

set_option autoImplicit false

namespace PoSUndirected.Supplement

/-- **Theorem 4.3 (sharp owner bound).** Tsoufis, preprint sha256 c095d811…, p.8
(PDF p.10).

One endpoint owner is present for every edge of an arbitrary nonempty owned subset.  At maximum
physical block rank three ordinary PoS is strictly below `1348/715`; that constant is the exact
class supremum, and with binary rational costs a cheapest equilibrium is computable in polynomial
time.

**Formalization Note.** Finite instances are standardized on `Fin n`, without restricting their
isomorphism types.  `OwnerRankClassSupremum` includes both the strict upper bound on every finite
instance and arbitrarily close lower instances.  The algorithm is a Mathlib multi-tape Turing
machine on the explicit binary graph, owned-set and rational-cost encoding. -/
theorem theorem_4_3 (I : OwnerRealInstance) (hI : I.Valid 3) :
    (∀ q : ℝ, OrdinaryPoSValue I.game I.c q → q < (1348 : ℝ) / 715) ∧
    OwnerRankClassSupremum 3 ((1348 : ℝ) / 715) ∧
    HasPolynomialCheapestOwnerAlgorithm 3 := by sorry

end PoSUndirected.Supplement
