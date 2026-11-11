-- Prove2me | Theorems.Thm_QuantumSepPoly_Frobenius_optimization_geometry
-- name    : QuantumSepPoly.Frobenius.optimization_geometry
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:11:59.277122+00:00
-- url     : https://prove2.me/theorems/d5cfce46-eeaa-4264-aeb9-f49697d0b51a
-- title:
--   Sections 2.4 and 4 — attained optimization domains
-- statement:
--   For every $d\ge1$, the source pure-product separable convex hull is nonempty and compact, and all its elements are density matrices. For every Hermitian $M$ and arbitrary matrix $R$, the support and distance are attained:
--   $$h_{\rm Sep}(M)=(x\otimes y)^*M(x\otimes y)=\max_{S\in\operatorname{Sep}}\operatorname{Tr}(MS),\qquad\operatorname{distSep}_d(R)=\|R-S_*\|_F.$$
--   The unit vectors $x,y$ and minimizing $S_*$ exist in their actual feasible sets. The normalized sphere maximum, its amplitude-bounded version for $\kappa\ge1$, and every nonempty finite-net penalized optimum are also attained. This exposes the extremum semantics used by the source, as a foundation rather than a numbered milestone.
--
--   Differences from the source:
--   - encoding: coordinates labelled 1 through d → coordinates indexed by Fin d from 0 through d-1; reason: canonical relabelling preserves all vectors, matrices, sums, and constraints
--   - encoding: maxima and minima over separable states and normalized vectors → explicit nonemptiness, compactness, attainment, and optimization inequalities for the computed suprema and infima; reason: exposes the source extremum conventions without assuming them
--   - generalization: distance for density inputs and quartic extrema for Section 4 matrices → distance for every complex matrix and extrema of real-part quartics for every complex matrix; reason: nonempty compact feasible sets give attainment for these continuous objectives; density inputs and all Section 4 matrices are included
-- source:
--   Giulio Malavolta, STOC 2027 submission #1577 (October 2026), Sections 2.4 and 4, p. 8 (PDF p. 8); §§2.4,4 pp.8,13,16–17 as applicable; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1577.pdf

import Definitions.Def_QuantumSepPoly_Frobenius_DiskNet

namespace QuantumSepPoly.Frobenius

/-- Extremum semantics of §2.4 and §4: no empty or unbounded real optimization set. -/
theorem optimization_geometry (d : ℕ) (hd : 0 < d) :
    (Sep d).Nonempty ∧ IsCompact (Sep d) ∧
    (∀ R ∈ Sep d, IsDensity R) ∧
    (∀ M : Bip d, M.IsHermitian →
      ∃ x y : Vec d, vecSq x = 1 ∧ vecSq y = 1 ∧
        productDensity x y ∈ Sep d ∧ support M = productValue M x y ∧
        (∀ R ∈ Sep d, (M*R).trace.re ≤ support M)) ∧
    (∀ R : Bip d, ∃ S ∈ Sep d, distanceSep R = frob (R-S) ∧
      ∀ T ∈ Sep d, distanceSep R ≤ frob (R-T)) ∧
    (∀ (M : Bip d) (κ : ℝ), 1 ≤ κ →
      (∃ x y : Vec d, vecSq x = d ∧ vecSq y = d ∧ sphereValue M = Q M x y) ∧
      (∃ x y : Vec d, vecSq x = d ∧ vecSq y = d ∧ AmplitudeBound κ x ∧ AmplitudeBound κ y ∧
        boundedSphereValue M κ = Q M x y)) ∧
    (∀ (M : Bip d) (lam : ℝ) (E : Finset ℂ), E.Nonempty →
      ∃ x y : Vec d, (∀ i, x i ∈ E) ∧ (∀ i, y i ∈ E) ∧
        discreteValue M lam E = penalty M lam x y) := by sorry

end QuantumSepPoly.Frobenius
