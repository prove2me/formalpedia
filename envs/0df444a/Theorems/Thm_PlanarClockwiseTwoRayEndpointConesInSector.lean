-- Prove2me | Theorems.Thm_PlanarClockwiseTwoRayEndpointConesInSector
-- name    : PlanarClockwiseTwoRayEndpointConesInSector
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T20:25:29.045008+00:00
-- url     : https://prove2.me/theorems/64f0eb85-ee00-4c82-bd6b-35afc29eafa3
-- title:
--   Planar Clockwise Two Ray Endpoint Cones In Sector
-- statement:
--   Let $p\in\mathbb R^2$, let $\rho>0$, and let $b,o\ne0$.  Suppose that
--   $$
--     o=c\,b-s\,\operatorname{rot}_{90}(b)
--     \qquad\text{with } s>0 .
--   $$
--   Thus $o$ lies strictly clockwise from $b$ in the
--   $(b,\operatorname{rot}_{90}(b))$-coordinates.  Define
--   $$
--     \Phi_b(x,y)=p+x\,b+y\,\operatorname{rot}_{90}(b)
--   $$
--   and
--   $$
--     \Sigma=\Phi_b\{(x,y):x^2+y^2<(\rho/\|b\|)^2,\ y<0,\
--       c y+s x>0\}.
--   $$
--   Then $\Sigma$ is open and connected, and there are $r>0$ and $K>0$
--   such that the terminal-side cone along $b$,
--   $$
--     \Phi_b\{(x,y):0<x,\ x^2+y^2<(r/\|b\|)^2,\ -Kx<y<0\},
--   $$
--   is contained in $\Sigma$, and the initial left cone along $o$,
--   $$
--     \Phi_o\{(u,v):0<u,\ u^2+v^2<(r/\|o\|)^2,\ 0<v<Ku\},
--     \quad
--     \Phi_o(u,v)=p+u\,o+v\,\operatorname{rot}_{90}(o),
--   $$
--   is also contained in $\Sigma$.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `PlanarClockwiseTwoRayEndpointConesInSector`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PlanarClockwiseTwoRayEndpointConesInSector.lean#L1-L301

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Definitions.Def_PlanarRot90

open Classical
noncomputable section

lemma PlanarClockwiseTwoRayEndpointConesInSector
    (p base other : EuclideanSpace ℝ (Fin 2)) (rho c s : ℝ)
    (hrho : 0 < rho) (hbase : base ≠ 0) (hother : other ≠ 0)
    (hs : 0 < s)
    (hother_eq : other = c • base - s • PlanarRot90 base) :
    let baseChart : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
      fun z => p + z 0 • base + z 1 • PlanarRot90 base
    let otherChart : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
      fun z => p + z 0 • other + z 1 • PlanarRot90 other
    let sector : Set (EuclideanSpace ℝ (Fin 2)) :=
      baseChart ''
        {z | z 0 ^ 2 + z 1 ^ 2 < (rho / ‖base‖) ^ 2 ∧
          z 1 < 0 ∧ 0 < c * z 1 + s * z 0}
    IsOpen sector ∧ IsConnected sector ∧
      ∃ r K : ℝ, 0 < r ∧ 0 < K ∧
        baseChart ''
            {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < (r / ‖base‖) ^ 2 ∧
              -K * z 0 < z 1 ∧ z 1 < 0} ⊆ sector ∧
          otherChart ''
            {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < (r / ‖other‖) ^ 2 ∧
              0 < z 1 ∧ z 1 < K * z 0} ⊆ sector := by sorry
