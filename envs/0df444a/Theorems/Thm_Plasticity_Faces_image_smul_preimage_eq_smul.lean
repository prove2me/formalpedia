-- Prove2me | Theorems.Thm_Plasticity_Faces_image_smul_preimage_eq_smul
-- name    : Plasticity.Faces.image_smul_preimage_eq_smul
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-15T00:33:59.331342+00:00
-- url     : https://prove2.me/theorems/bfa71987-7095-4b8d-9c63-5975a074ea00
-- title:
--   A compact preimage face is carried onto the face at every scale
-- statement:
--   Let $F\colon B_X\to B_Y$ be a nonexpansive bijection of the unit balls of real normed spaces and $C$ a finite-dimensional sphere face of $B_Y$ whose preimage $D=B_X\cap F^{-1}(C)$ is compact. Then $$F(tD)=tC\qquad(0\le t\le1).$$
-- source:
--   This repository: expositions/faces/codirected_compactness.md (claim F11), Proposition 4

import Definitions.Def_Plasticity_Faces
import Mathlib.Topology.EMetricSpace.Lipschitz

namespace Plasticity.Faces
open scoped Pointwise
theorem image_smul_preimage_eq_smul {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : X → Y)
    (hbij : Set.BijOn F (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : Y) 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1))
    (C : Set Y) (hC : IsSphereFace C) (hfin : FiniteDimensional ℝ (vectorSpan ℝ C))
    (hD : IsCompact (Metric.closedBall (0 : X) 1 ∩ F ⁻¹' C)) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      F '' (t • (Metric.closedBall (0 : X) 1 ∩ F ⁻¹' C)) = t • C := by sorry
end Plasticity.Faces
