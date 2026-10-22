-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P01_finiteGroup_irrep_factor_operations
-- name    : QAlgorithms.Papers.Independent.Gap20.P01.finiteGroup_irrep_factor_operations
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T20:14:32.759671+00:00
-- url     : https://prove2.me/theorems/c2c72777-7ae9-45dd-8ba1-12bc197ee0b3
-- title:
--   Extract, operate on the irrep factor, and reverse extraction
-- statement:
--   Let $G$, $r_\mu$, $R$ and its complete orthonormal reducing basis be as in finite-group irrep measurement. Let $X=(F^-\otimes I)\,\mathrm{C}R\,((F^-)^\dagger\otimes I)$ be the corrected extraction circuit, and let $|t\rangle$ be the auxiliary trivial-irrep coefficient. For each $\mu$, let $A_\mu$ be a unitary operation on its irrep coordinates. Let $\widetilde A$ apply $A_\mu$ to the extracted $\alpha$ coordinate controlled by $\mu$, leaving $\beta$ unchanged, and define the physical operation $A_R$ by $A_R=\bigoplus_\mu(I_{n_\mu}\otimes A_\mu)$ in the independently chosen reducing basis. Then for every physical vector,
--
--   $$
--   X^\dagger(\widetilde A\otimes I)X\bigl(|t\rangle\otimes|\psi\rangle\bigr)=|t\rangle\otimes A_R|\psi\rangle.
--   $$
--
--   Thus extraction and its inverse allow available controlled operations on the irrep factor, coherently across irrep labels, with multiplicity coordinates untouched and the auxiliary register restored. The statement charges no fictitious efficiency to arbitrary matrices $A_\mu$: their implementations are additional supplied operations.
-- source:
--   Efficient Quantum Circuits for Schur and Clebsch-Gordan Transforms, arXiv:quant-ph/0407082v4, PDF p. 4, Last paragraph before Conclusion

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P01

noncomputable section

open scoped BigOperators Matrix Kronecker ComplexConjugate

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Gap20.P01

open QAlgorithms.Papers.Independent.Support21.P09 (Rep UnitaryRep elementaryGates)

variable {G L I : Type} [Group G] [Fintype G] [Fintype L]
  [Fintype I]

/-- PDF p.4, last paragraph: extract, apply an available controlled irrep
operation, and reverse extraction. The auxiliary register is restored,
multiplicity coordinates are untouched, and the identity is coherent across
all irrep labels. The Fourier convention correction is the one explicitly
specified in fourierMinus. This does not assert efficient arbitrary A_mu. -/
theorem finiteGroup_irrep_factor_operations (D : FiniteDual G L)
    (R : Rep G I) (hR : UnitaryRep R) (B : ReducingBasis D R)
    (A : ∀ a, Matrix.unitaryGroup (Fin (D.irrep a).dim) ℂ) :
    ∀ psi : EuclideanSpace ℂ I,
      act ((figureThree D R)ᴴ *
        (auxiliaryFactor D A ⊗ₖ (1 : Matrix I I ℂ)) * figureThree D R)
        (tensorVec (auxiliaryStart D) psi) =
      tensorVec (auxiliaryStart D) (act (physicalFactor D R B A) psi) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P01

end
