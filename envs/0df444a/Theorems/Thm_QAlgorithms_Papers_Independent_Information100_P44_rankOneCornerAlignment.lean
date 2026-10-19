-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P44_rankOneCornerAlignment
-- name    : QAlgorithms.Papers.Independent.Information100.P44.rankOneCornerAlignment
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:41:08.864989+00:00
-- url     : https://prove2.me/theorems/ac322100-473f-4f04-bf30-a6f391983367
-- title:
--   Corollary 5: rank-one corner forces alignment
-- statement:
--   Let $A,C$ be finite square complex matrices and $B$ a compatible rectangular matrix. Suppose $\psi\ne0$, with no unit-norm requirement, and
--   $$\begin{pmatrix}A&B\\B^\dagger&C\end{pmatrix}\succeq0,\qquad A=|\psi\rangle\langle\psi|.$$
--   Then $\operatorname{Ran}B\subseteq\mathbb C\psi$. This forces all coupled data into the one-dimensional range of the rank-one corner.
-- source:
--   Limitations on Joint Coherence Transfer in Quantum Thermodynamics, arXiv:2608.11872v1, PDF p. 21, Corollary 5: rank-one corner forces alignment

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P44

namespace QAlgorithms.Papers.Independent.Information100.P44

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

/-- PDF p.21, Corollary 5: an unnormalized nonzero rank-one corner aligns all of B. -/
theorem rankOneCornerAlignment {d n : ℕ} (A : Mat d) (B : Matrix (Fin d) (Fin n) ℂ)
    (C : Mat n) (psi : EuclideanSpace ℂ (Fin d)) (hpsi : psi ≠ 0)
    (hA : A = pureDensity psi) (hpos : (Matrix.fromBlocks A B Bᴴ C).PosSemidef) :
    Set.range B.mulVec ⊆ {x | ∃ a : ℂ, x = a • (fun i => psi i)} := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P44
