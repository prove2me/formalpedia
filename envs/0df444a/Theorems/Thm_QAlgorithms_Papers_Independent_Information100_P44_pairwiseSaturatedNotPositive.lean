-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P44_pairwiseSaturatedNotPositive
-- name    : QAlgorithms.Papers.Independent.Information100.P44.pairwiseSaturatedNotPositive
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:41:40.299275+00:00
-- url     : https://prove2.me/theorems/bf178037-17ba-4fff-8f8d-6da445e15845
-- title:
--   Proposition 4: pairwise saturated Gram data need not glue
-- statement:
--   Consider the fixed complex Hermitian matrix
--   $$M_{\rm fr}=\begin{pmatrix}1&-1&1\\-1&1&1\\1&1&1\end{pmatrix}.$$
--   Every two-by-two principal submatrix is positive semidefinite and has rank one, whereas $M_{\rm fr}$ is not positive semidefinite. This exhibits an incompatibility of pairwise saturated Gram data independent of energy-level degeneracy.
-- source:
--   Limitations on Joint Coherence Transfer in Quantum Thermodynamics, arXiv:2608.11872v1, PDF p. 22, Proposition 4: pairwise saturated Gram data need not glue

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P44

namespace QAlgorithms.Papers.Independent.Information100.P44

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

/-- PDF p.22, Proposition 4: pairwise rank-one positivity fails to glue for the fixed matrix. -/
theorem pairwiseSaturatedNotPositive :
    (∀ f : Fin 2 ↪ Fin 3,
      (frustration.submatrix f f).PosSemidef ∧ (frustration.submatrix f f).rank = 1) ∧
    ¬ frustration.PosSemidef := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P44
