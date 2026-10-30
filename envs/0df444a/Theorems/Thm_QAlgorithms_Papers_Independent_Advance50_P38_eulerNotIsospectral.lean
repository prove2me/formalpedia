-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P38_eulerNotIsospectral
-- name    : QAlgorithms.Papers.Independent.Advance50.P38.eulerNotIsospectral
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T08:56:02.557264+00:00
-- url     : https://prove2.me/theorems/dd695bd4-67b5-48a7-a25c-4870d14a14a7
-- title:
--   Remark III.8: Euler iteration need not preserve the spectrum
-- statement:
--   The standard Euler step for the double-bracket field need not preserve the spectrum. More precisely, there exist Hermitian complex $2$ by $2$ matrices $X,C$ such that, for every real $\alpha>0$,
--   $$\chi_{X+\alpha[X,S([X,C^\dagger])]}\ne\chi_X,$$
--   where $S(D)=(D-D^\dagger)/2$ and $\chi$ denotes the characteristic polynomial. Every $X$ belongs to its own unitary orbit. This existential failure statement makes no claim about all Euler steps.
-- source:
--   Gradient Flows for Optimisation and Quantum Control: Foundations and Applications, arXiv:0802.4195v2, PDF p. 25, Remark III.8: Euler iteration need not preserve the spectrum

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P38

namespace QAlgorithms.Papers.Independent.Advance50.P38

open scoped BigOperators Topology Manifold ContDiff

noncomputable section

/-- Remark III.8, PDF p.25: a Hermitian two-dimensional witness that
standard Euler integration need not preserve the spectrum. -/
theorem eulerNotIsospectral :
    ∃ X C : (Matrix (Fin 2) (Fin 2) ℂ), X.IsHermitian ∧ C.IsHermitian ∧
      ∀ a : ℝ, 0 < a → (orbitEulerStep X C a).charpoly ≠ X.charpoly := by sorry

end

end QAlgorithms.Papers.Independent.Advance50.P38
