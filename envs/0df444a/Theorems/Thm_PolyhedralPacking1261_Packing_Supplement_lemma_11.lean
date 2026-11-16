-- Prove2me | Theorems.Thm_PolyhedralPacking1261_Packing_Supplement_lemma_11
-- name    : PolyhedralPacking1261.Packing.Supplement.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T06:42:40.250411+00:00
-- url     : https://prove2.me/theorems/92c4a958-fbe0-4ded-9836-72cc9b4e6953
-- title:
--   Lemma 11 — each $2T_I(Q_i)$ contains a $\delta$-tube, with directions $\delta$-separated in each slope group
-- statement:
--   In the setting of Section 3 (as in Lemma 10), let $I$ be a retained interval with midpoint $u_I$, let $T_I(x,y,z)=(bx-u_Iy,\ \tau y,\ z/c)$, let $D_i=(b(v_i-k_iu_I),\,k_ib\tau,\,1)$, $d_i=D_i/\|D_i\|$ and $\delta=b\tau/1000$. Then within each retained slope group:
--
--   1. every $2T_I(Q_i)$ contains the tube $S_i=T_\delta\big(d_i,\,2T_I(p_i)\big)$, and
--   2. for $i\ne j$ the unoriented angle between $d_i$ and $d_j$ is at least $\delta$.
--
--   Here $2T_I(Q_i)$ is the image of $Q_i$ under $x\mapsto 2T_I(x)$. The lemma turns each slope group into a family of direction-separated tubes, to which Theorem 4 applies in the proof of Theorem 8.
--
--   Differences from the source:
--   - generalization: the label containing the most u_i-values; an unspecified cut of the line → every label L ∈ ℤ and every grid offset θ; reason: the argument uses only membership of u_i in one interval of length τ/100; the most populated label is one instance
--   - encoding: intervals, retained objects, slope groups → as in Lemma 10 (slopeInterval, Retained, intervalMidpoint); reason: same convention as Lemma 10
--   - encoding: tubes and angles in ℝ³ → the coordinate triples are identified with EuclideanSpace ℝ (Fin 3) by toE3; tube and angle are Euclidean; reason: the identification is the identity on coordinates and an isometry for the Euclidean norm
-- source:
--   Simon Bartlmae, Anders Aamand, Mikkel Abrahamsen, Polylogarithmic Approximation for Packing Convex Polyhedra, STOC 2027 submission #1261 (October 2026), canonical PDF SHA-256 b915da2d5fece730ea9946885b05ad09e10e575374e6a1df96e8a6149cb0e67e, Lemma 11, the map T_I, (4), D_i and d_i, §3, PDF pp.13–14 (printed pp.12–13)

import Definitions.Def_PolyhedralPacking1261_Packing_Supplement_SlopeGroups

set_option autoImplicit false

namespace PolyhedralPacking1261.Packing.Supplement

open PolyhedralPacking1261.Packing

/-- Lemma 11, PDF p.14 (printed p.13). In the setting of Section 3, with `δ = bτ/1000`,
for every retained object `i` in the interval `I` with midpoint `u_I`, the image
`2T_I(Q_i)` contains the open tube `T_δ(d_i, 2T_I(p_i))`; and for distinct retained
objects in the same interval the unoriented angle between `d_i` and `d_j` is at least
`δ`. -/
theorem lemma_11 (b c τ θ : ℝ) (L : ℤ) {m : ℕ} (P : Fin m → BCParameters)
    (p : Fin m → Point3) (hset : LowerBoundSetting b c τ P p) :
    (∀ i, Retained θ τ L (P i) →
      tube (b * τ / 1000)
          (tubeDirection b τ (intervalMidpoint θ τ (slopeInterval θ τ (P i).u)) (P i))
          (toE3 ((2 : ℝ) • slopeMap b c τ
            (intervalMidpoint θ τ (slopeInterval θ τ (P i).u)) (p i))) ⊆
        toE3 '' ((fun x => (2 : ℝ) • slopeMap b c τ
            (intervalMidpoint θ τ (slopeInterval θ τ (P i).u)) x) ''
          auxBody b c τ (P i) (p i))) ∧
    (∀ i j, i ≠ j → Retained θ τ L (P i) → Retained θ τ L (P j) →
      slopeInterval θ τ (P i).u = slopeInterval θ τ (P j).u →
      b * τ / 1000 ≤ unorientedAngle
        (tubeDirection b τ (intervalMidpoint θ τ (slopeInterval θ τ (P i).u)) (P i))
        (tubeDirection b τ (intervalMidpoint θ τ (slopeInterval θ τ (P j).u)) (P j))) := by sorry

end PolyhedralPacking1261.Packing.Supplement
