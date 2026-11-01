-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P13_regularPoint_inTetrahedron
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P13.regularPoint_inTetrahedron
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:59:56.577009+00:00
-- url     : https://prove2.me/theorems/5c8b110a-d99d-47dc-a3ea-5e1cd6fc838d
-- title:
--   Regular contracted S coordinates are valid Pauli points
-- statement:
--   Let $\gamma,s\in[0,1]$ and assume $1-\gamma s>0$, the domain of the displayed real quotient. Let $T$ be the convex hull of the four Bell-correlation vectors $(1,-1,1),(1,1,-1),(-1,-1,-1),(-1,1,1)$, and suppose $v=(S_{11},S_{22},S_{33})\in T$. The point constructed from the positive-translation rescaling satisfies
--
--   $$\left(\sqrt{\frac{1-\gamma}{1-\gamma s}}S_{11},\sqrt{\frac{1-\gamma}{1-\gamma s}}S_{22},\frac{1-\gamma}{1-\gamma s}S_{33}\right)\in T.$$
--
--   Here $s=S_{30}$ in the application. This is a computed point, and no unrelated free Pauli parameters are assumed.
-- source:
--   Simulation of non-Pauli Channels, arXiv:1706.05384v2, PDF p. 13, Corollary 23, Eq.(C3)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P13

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakethird100.P13

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:1706.05384v2 PDF pp.12--13, Corollary 23, Eq.(C3), positive S30 case.
The constructed point uses the regular quotient domain of Lemma 20. -/
theorem regularPoint_inTetrahedron (gamma s30 : ℝ) (hg0 : 0 ≤ gamma) (hg1 : gamma ≤ 1)
    (hs0 : 0 ≤ s30) (hs1 : s30 ≤ 1) (hden : 0 < 1-gamma*s30)
    (s : BlochCoordinates) (hs : s ∈ pauliTetrahedron) :
    regularPauliPoint gamma s30 s ∈ pauliTetrahedron := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P13

end
