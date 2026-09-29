-- Prove2me | Theorems.Thm_PlanarSlitDiskEndpointConesAvoidRay
-- name    : PlanarSlitDiskEndpointConesAvoidRay
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T22:17:55.940988+00:00
-- url     : https://prove2.me/theorems/60a283e3-7725-44a3-9910-0e0312648532
-- title:
--   Endpoint cones in a planar slit disk avoid the deleted ray
-- statement:
--   Let $p$ be a point, let $base
--   e0$ be a direction, and let $ho>0$. Remove from the open disk $B(p,ho)$ the positive ray from $p$ in direction $base$ and the point $p$ itself. The resulting slit disk is open and connected, and it contains two small endpoint cones on the two sides of the slit. More precisely, in the orthogonal chart
--   $$
--   z\longmapsto p+z_0\,base+z_1\,\operatorname{PlanarRot90}(base),
--   $$
--   there are positive $r$ and $K$ for which the lower and upper wedges are contained in the slit disk.
--
--   This supplies the connected local terminal neighborhood and the two cone inclusions used by the terminal-slit-disk construction.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PlanarSlitDiskEndpointConesAvoidRay.lean#L1-380

import Definitions.Def_PlanarRot90

open Classical
noncomputable section

lemma PlanarSlitDiskEndpointConesAvoidRay
    (p base : EuclideanSpace ℝ (Fin 2)) (rho : ℝ)
    (hrho : 0 < rho) (hbase : base ≠ 0) :
    let ray : Set (EuclideanSpace ℝ (Fin 2)) :=
      {q | ∃ t : ℝ, 0 < t ∧ q = p + t • base}
    let slit : Set (EuclideanSpace ℝ (Fin 2)) :=
      Metric.ball p rho \ (ray ∪ ({p} : Set (EuclideanSpace ℝ (Fin 2))))
    let chart : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
      fun z => p + z 0 • base + z 1 • PlanarRot90 base
    IsOpen slit ∧ IsConnected slit ∧
      ∃ r K : ℝ, 0 < r ∧ 0 < K ∧
        chart ''
            {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < (r / ‖base‖) ^ 2 ∧
              -K * z 0 < z 1 ∧ z 1 < 0} ⊆ slit ∧
          chart ''
            {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < (r / ‖base‖) ^ 2 ∧
              0 < z 1 ∧ z 1 < K * z 0} ⊆ slit := by sorry
