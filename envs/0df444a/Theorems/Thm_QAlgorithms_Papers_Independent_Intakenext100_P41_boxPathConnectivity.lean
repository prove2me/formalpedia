-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P41_boxPathConnectivity
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P41.boxPathConnectivity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:36:07.645214+00:00
-- url     : https://prove2.me/theorems/f0f85521-76f9-42d6-a784-241835ea03e6
-- title:
--   Connectivity of permissible box paths
-- statement:
--   Let $N\ge2$, $\ell\ge1$, and $1\le k\le N$. A permissible signature is a weakly decreasing integral $N$-tuple with largest-minus-smallest entry at most $\ell$. Fix signatures $f,g$ and two length-$k$ paths from $f$ to $g$, each step adding one box to one row and every intermediate signature permissible. Two paths are adjacent when exactly one interior signature changes. Then
--
--   $$\text{there is a finite chain of adjacent paths from the first path to the second.}$$
--
--   All paths in the chain have the same endpoints and length. Signatures are kept unnormalized until any final common-shift equivalence; at $k=1$ the chain can have length zero.
-- source:
--   Operator Algebras and Conformal Field Theory III. Fusion of positive energy representations of LSU(N) using bounded operators, arXiv:math/9806031v1, PDF p. 42, §32: We complete the proof by showing by induction on k

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P41

noncomputable section

open scoped BigOperators

open MeasureTheory Set

namespace QAlgorithms.Papers.Independent.Intakenext100.P41

/-- §32, final combinatorial argument, PDF p.42: paths with the same endpoints
and length are connected by single-intermediate-signature changes. All vertices
are actual permissible signatures, not independently normalized representatives. -/
theorem boxPathConnectivity (N ell k : ℕ) (hN : 2 ≤ N) (hell : 1 ≤ ell)
    (hk : 1 ≤ k) (hkN : k ≤ N) (f g : IntegerSignature N)
    (P Q : BoxPath ell k f g) :
    Relation.ReflTransGen AdjacentPaths P Q := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P41

end
