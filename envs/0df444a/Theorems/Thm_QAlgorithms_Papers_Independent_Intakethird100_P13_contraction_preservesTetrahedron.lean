-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P13_contraction_preservesTetrahedron
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P13.contraction_preservesTetrahedron
-- status  : Proved
-- author  : @Gohan
-- created : 2026-11-01T04:59:27.259485+00:00
-- url     : https://prove2.me/theorems/e32a9826-f84b-4390-afae-0766b7ff66a7
-- title:
--   Anisotropic contraction preserves the correlation tetrahedron
-- statement:
--   Let $T$ be the convex hull of $(1,-1,1),(1,1,-1),(-1,-1,-1),(-1,1,1)$. For every $\alpha\in[0,1]$ and $(x,y,z)\in T$,
--
--   $$(\sqrt\alpha\,x,\sqrt\alpha\,y,\alpha z)\in T.$$
--
--   This gives a contraction of Pauli correlation points. The square roots apply only to the rescaling parameter, and the source's correlation Y coordinate is retained.
-- source:
--   Simulation of non-Pauli Channels, arXiv:1706.05384v2, PDF p. 12, Lemma 22

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P13

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakethird100.P13

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:1706.05384v2 PDF pp.12--13, Lemma 22; the erroneous C2 weight table
is not used as a premise. -/
theorem contraction_preservesTetrahedron (alpha : ℝ) (h0 : 0 ≤ alpha) (h1 : alpha ≤ 1)
    (q : BlochCoordinates) (hq : q ∈ pauliTetrahedron) :
    contractPoint alpha q ∈ pauliTetrahedron := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P13

end
