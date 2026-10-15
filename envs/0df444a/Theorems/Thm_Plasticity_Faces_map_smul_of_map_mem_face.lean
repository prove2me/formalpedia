-- Prove2me | Theorems.Thm_Plasticity_Faces_map_smul_of_map_mem_face
-- name    : Plasticity.Faces.map_smul_of_map_mem_face
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-15T02:22:51.774798+00:00
-- url     : https://prove2.me/theorems/fff25dca-9837-4fb0-bc7f-232cdd91a12f
-- title:
--   A nonexpansive ball bijection that keeps the sphere is homogeneous at every preimage of a point of a finite-dimensional face
-- statement:
--   Let $X,Y$ be real normed spaces and $F$ a map that is nonexpansive and injective on $B_X$, with $B_Y\subseteq F(B_X)$ (so that $F$ maps $B_X$ bijectively onto $B_Y$) and $F(S_X)\subseteq S_Y$. If $C$ is a finite-dimensional face of $B_Y$ contained in the sphere and $F(x)\in C$ for some $x\in B_X$, then $F(tx)=tF(x)$ for every $t\in[-1,1]$.
--   By induction on $\dim C$: the face theorem gives the preimage face $D$ and $F(tD)=tC$; boundary preimages are homogeneous by induction, so $F$ is isometric between them (card `Plasticity.BallMap.norm_map_sub_map_eq_of_map_smul`), hence isometric on $tD$ along chords, and $F(tx)/t$ and $F(x)$ have the same distances to every boundary point of $C$.
-- source:
--   C. Angosto, V. Kadets, O. Zavarzina, J. Math. Anal. Appl. 471 (2019), proof of Theorem 4.11 (arXiv:1808.08534), with the face theorem of claim F17 (card Plasticity.Faces.matchesFace_of_finiteDimensional) in place of their Theorems 4.8–4.9; expositions/faces/finite_faces_boundary_crossing.md §6

import Definitions.Def_Plasticity_Faces
import Mathlib.Topology.EMetricSpace.Lipschitz

namespace Plasticity.Faces
theorem map_smul_of_map_mem_face {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : X → Y)
    (hinj : Set.InjOn F (Metric.closedBall (0 : X) 1))
    (hsurj : Set.SurjOn F (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : Y) 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1))
    (hsphere : Set.MapsTo F (Metric.sphere (0 : X) 1) (Metric.sphere (0 : Y) 1))
    (C : Set Y) (hC : IsSphereFace C) (hfin : FiniteDimensional ℝ (vectorSpan ℝ C))
    (x : X) (hx : x ∈ Metric.closedBall (0 : X) 1) (hFx : F x ∈ C) :
    ∀ t ∈ Set.Icc (-1 : ℝ) 1, F (t • x) = t • F x := by sorry
end Plasticity.Faces
