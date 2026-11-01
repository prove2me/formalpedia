-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P13_diagonalS_inTetrahedron
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P13.diagonalS_inTetrahedron
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:00:56.21409+00:00
-- url     : https://prove2.me/theorems/8f7ad310-4908-4c39-82b2-d0e43b87139f
-- title:
--   Every classical channel gives a diagonal S point in T
-- statement:
--   Let $p(l\mid k)$ be any nonnegative conditional law on four symbols, with $\sum_l p(l\mid k)=1$ separately for each input $k$. Define $S_{ij}$ by Eq. (38), including its factor $1/4$ and six-delta exponent. For the Bell-correlation tetrahedron $T=\operatorname{conv}\{(1,-1,1),(1,1,-1),(-1,-1,-1),(-1,1,1)\}$,
--
--   $$(S_{11},S_{22},S_{33})\in T.$$
--
--   This assertion requires neither a resource state nor a damping parameter. It covers all conditional channels, including laws that are not doubly stochastic.
-- source:
--   Simulation of non-Pauli Channels, arXiv:1706.05384v2, PDF p. 13, Lemma 24

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P13

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakethird100.P13

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:1706.05384v2 PDF pp.5,13, Lemma 24: no resource or damping assumption.
Eq.(38)'s normalization, rather than Appendix B's omitted factor, defines S. -/
theorem diagonalS_inTetrahedron (p : Fin 4 → Fin 4 → ℝ) (hp : ClassicalTeleportationLaw p) :
    (fun i : Fin 3 => sCoordinate p i i.succ) ∈ pauliTetrahedron := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P13

end
