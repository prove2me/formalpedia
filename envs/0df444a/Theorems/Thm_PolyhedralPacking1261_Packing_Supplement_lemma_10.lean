-- Prove2me | Theorems.Thm_PolyhedralPacking1261_Packing_Supplement_lemma_10
-- name    : PolyhedralPacking1261.Packing.Supplement.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T06:41:56.887543+00:00
-- url     : https://prove2.me/theorems/60873484-6d81-4de4-a498-da87f2db9e06
-- title:
--   Lemma 10 — auxiliary bodies of different retained slope groups have disjoint interiors and lie in $[-\tau/200,1+\tau/200]\times[0,1]^2$
-- statement:
--   Fix the setting of Section 3: bc-parallelepipeds $P_1,\dots,P_m$ of one type ($b,c>0$, each fitting individually in the unit cube), placed with centers $p_i$ as a translational packing in $[0,1]^3$, and $0<\tau\le2$ with $d(i,j)>\tau$ for distinct $i,j$ with $k_i=k_j$. Cut the line into intervals of length $\tau/100$ labelled cyclically $1,\dots,10$, and retain the objects with $a_i<\tau/100$ whose $u_i$ lies in an interval of a fixed label. For each retained object let $Q_i$ be the auxiliary body (3). Then
--
--   1. auxiliary bodies from different retained slope groups (different intervals) have disjoint interiors, and
--   2. every $Q_i$ lies in $[-\tau/200,\,1+\tau/200]\times[0,1]^2$.
--
--   The paper applies this with the most populated label; the statement holds for every label and every placement of the interval grid. It allows the volume bounds of different slope groups to be added in the proof of Theorem 8.
--
--   Differences from the source:
--   - generalization: the label containing the most u_i-values; an unspecified cut of the line → every label L ∈ ℤ and every grid offset θ; reason: the argument uses only that two intervals of one label are 9τ/100 apart; the most populated label is one instance
--   - encoding: intervals of length τ/100 labelled 1,…,10 from left to right → half-open intervals [θ + jτ/100, θ + (j+1)τ/100), label j mod 10, slope group = interval index; retained = a < τ/100 and label L; reason: a fixed convention for the source's partition; same retained families
--   - encoding: the fixed family, packing and separation of Section 3 → LowerBoundSetting b c τ P p with explicit centers p; reason: the standing assumptions of §§2–3 as one hypothesis
-- source:
--   Simon Bartlmae, Anders Aamand, Mikkel Abrahamsen, Polylogarithmic Approximation for Packing Convex Polyhedra, STOC 2027 submission #1261 (October 2026), canonical PDF SHA-256 b915da2d5fece730ea9946885b05ad09e10e575374e6a1df96e8a6149cb0e67e, Lemma 10 and auxiliary bodies (3), §3, PDF p.12 (printed p.11)

import Definitions.Def_PolyhedralPacking1261_Packing_Supplement_SlopeGroups

set_option autoImplicit false

namespace PolyhedralPacking1261.Packing.Supplement

open PolyhedralPacking1261.Packing

/-- Lemma 10, PDF p.12 (printed p.11). In the setting of Section 3, for any partition of
the line into intervals of length `τ/100` (offset `θ`) and any label `L` (in particular
the most populated one), auxiliary bodies of retained objects lying in different
intervals have disjoint interiors, and every retained auxiliary body lies in
`[−τ/200, 1 + τ/200] × [0,1]²`. -/
theorem lemma_10 (b c τ θ : ℝ) (L : ℤ) {m : ℕ} (P : Fin m → BCParameters)
    (p : Fin m → Point3) (hset : LowerBoundSetting b c τ P p) :
    (∀ i j, Retained θ τ L (P i) → Retained θ τ L (P j) →
      slopeInterval θ τ (P i).u ≠ slopeInterval θ τ (P j).u →
      Disjoint (interior (auxBody b c τ (P i) (p i)))
        (interior (auxBody b c τ (P j) (p j)))) ∧
    (∀ i, Retained θ τ L (P i) →
      auxBody b c τ (P i) (p i) ⊆
        closedBox ![-(τ / 200), 0, 0] ![1 + τ / 200, 1, 1]) := by sorry

end PolyhedralPacking1261.Packing.Supplement
