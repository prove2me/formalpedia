-- Prove2me | Theorems.Thm_Plasticity_Ext_FreudenthalHurewicz
-- name    : Plasticity.Ext.FreudenthalHurewicz
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-14T09:01:19.324029+00:00
-- url     : https://prove2.me/theorems/87d7a875-2029-464c-a3b9-5288a5129719
-- title:
--   Freudenthal–Hurewicz: a nonexpansive surjection of a compact metric space onto itself is an isometry
-- statement:
--   Let $K$ be a compact subset of a metric space $M$ and $f\colon K\to K$ a map of $K$ onto itself with $d(f(x),f(y))\le d(x,y)$ for all $x,y\in K$. Then
--   $$d(f(x),f(y))=d(x,y)\qquad(x,y\in K).$$
--
--   Every totally bounded metric space is plastic by this argument; here it is used on finite-dimensional cubes.
--
--   **Formalization Note** $f$ is a function on $M$, constrained on $K$ by `Set.MapsTo`, `Set.SurjOn` and `LipschitzOnWith 1`.
-- source:
--   H. Freudenthal and W. Hurewicz, Dehnungen, Verkürzungen, Isometrien, Fund. Math. 26 (1936), 120–122; also Naimpally–Piotrowski–Wingler, J. Math. Anal. Appl. 313 (2006)

import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.EMetricSpace.Lipschitz

namespace Plasticity.Ext
theorem FreudenthalHurewicz {M : Type*} [MetricSpace M] (K : Set M) (hK : IsCompact K)
    (f : M → M) (hmaps : Set.MapsTo f K K) (hsurj : Set.SurjOn f K K)
    (hlip : LipschitzOnWith 1 f K) :
    ∀ x ∈ K, ∀ y ∈ K, dist (f x) (f y) = dist x y := by sorry
end Plasticity.Ext
