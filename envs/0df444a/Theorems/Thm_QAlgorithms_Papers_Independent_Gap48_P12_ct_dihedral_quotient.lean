-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P12_ct_dihedral_quotient
-- name    : QAlgorithms.Papers.Independent.Gap48.P12.ct_dihedral_quotient
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:35:32.78655+00:00
-- url     : https://prove2.me/theorems/053701d2-4588-4eb9-bc27-32b24c55f2b5
-- title:
--   Section 4.1, unnumbered: dihedral quotient (phase typo corrected)
-- statement:
--   Let $C_T(C_1)=\{TgT^{-1}:g,TgT^{-1}\in C_1\}$ for the exact Clifford group $C_1$. With the source's scalar typo corrected, put
--
--   $$K=\{e^{i\pi k/4}I: k=0,1,\ldots,7\}.$$
--
--   Then $K$ is the scalar normal subgroup of $C_T(C_1)$, and
--
--   $$C_T(C_1)/K\cong D_4,$$
--
--   where $D_4$ is the order-eight symmetry group of a square. The Lean statement identifies the carrier of the constructed ambient subgroup and the carrier of its constructed normal kernel before asserting a multiplicative isomorphism. The printed denominator $8$ would give a set that is not closed; denominator $4$ agrees with the exact symbolic generator $(HP^3)^3=e^{-i\pi/4}I$. This correction requires independent moderation.
-- source:
--   Representation of Quantum Circuits with Clifford and $π/8$ Gates, arXiv:0806.3834v1, PDF p. 7, Section 4.1, unnumbered: dihedral quotient (phase typo corrected)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P12

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P12

local notation "Mat" => Matrix Bool Bool ℂ

local notation "Vec" => EuclideanSpace ℂ Bool

local notation "wordMatrix" => fun (B : CircuitBasis) (w : CircuitWord) =>
  QAlgorithms.Papers.Independent.Next46.P21.wordMatrix (chronologicalInstructions B w)

/-- PDF p.7, §4.1: quotient by the scalar subgroup is D₄ (order eight).
Printed: K={exp(i*pi*k/8) I : k=0,...,7}; changed: denominator 4.
Why: the printed set omits the eighth power -I of its generator and is not
a subgroup. The corrected roots agree with (H P^3)^3=exp(-i*pi/4) I and
the stated orders 64 and 8. Carrier equalities are conclusions, so neither
subgroup closure nor the scalar correction is smuggled in as a hypothesis.
Independent moderation of this source correction is required. -/
theorem ct_dihedral_quotient :
    (ctGroup : Set (Matrix.unitaryGroup Bool ℂ)) = {u : Matrix.unitaryGroup Bool ℂ | (u : Mat) ∈ ctSet} ∧
    (∀ g : ctGroup, g ∈ scalarKernel ↔ ∃ k : Fin 8,
      (((g : ctGroup) : Matrix.unitaryGroup Bool ℂ) : Mat) = scalarRoot k) ∧
    Nonempty ((ctGroup ⧸ scalarKernel) ≃* DihedralGroup 4) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P12

end
