-- Prove2me | Theorems.Thm_Plasticity_Faces_exists_common_face_of_preimages
-- name    : Plasticity.Faces.exists_common_face_of_preimages
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-15T00:33:57.421502+00:00
-- url     : https://prove2.me/theorems/125eaded-ee22-4c6a-807d-faf9ce873ddb
-- title:
--   Preimages of points of a finite-dimensional face and of its reflection lie in a common face of no larger dimension
-- statement:
--   Let $X,Y$ be real normed spaces, $F\colon B_X\to B_Y$ a nonexpansive bijection, and $C$ a finite-dimensional face of $B_Y$ contained in the sphere, of dimension $n$. If $u,v\in B_X$ satisfy $F(u)\in C$ and $-F(-v)\in C$, then $u$ and $v$ lie in a common face of $B_X$ contained in the sphere, of dimension at most $n$.
--   The proof: $u$ and $v$ are codirected ($\|u+v\|=2$); $F$ maps their lens $\{h\in B_X:\|u-h\|\le1,\ \|v+h\|\le1\}$, which spans the directions of the smallest common face of $u$ and $v$, into $\operatorname{span}(C-C)$; invariance of dimension bounds that face's dimension by $n$.
-- source:
--   This repository: expositions/faces/finite_faces_boundary_crossing.md §2, (2.1)–(2.3), with expositions/faces/abstract_lenses.md §2, display (2.3) (claim F12)

import Definitions.Def_Plasticity_Faces
import Mathlib.Topology.EMetricSpace.Lipschitz

namespace Plasticity.Faces
theorem exists_common_face_of_preimages {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : X → Y)
    (hbij : Set.BijOn F (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : Y) 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1))
    (C : Set Y) (hC : IsSphereFace C) (hfin : FiniteDimensional ℝ (vectorSpan ℝ C))
    (u v : X) (hu : u ∈ Metric.closedBall (0 : X) 1) (hv : v ∈ Metric.closedBall (0 : X) 1)
    (hFu : F u ∈ C) (hFv : -F (-v) ∈ C) :
    ∃ E : Set X, IsSphereFace E ∧ FiniteDimensional ℝ (vectorSpan ℝ E) ∧
      Module.finrank ℝ (vectorSpan ℝ E) ≤ Module.finrank ℝ (vectorSpan ℝ C) ∧ u ∈ E ∧ v ∈ E := by sorry
end Plasticity.Faces
