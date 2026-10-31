-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P52_rotated_entangled_contraction
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P52.rotated_entangled_contraction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:31:49.712131+00:00
-- url     : https://prove2.me/theorems/a542a518-0383-43a8-8628-79dc8e13f1be
-- title:
--   Lemma 2: rotated maximally entangled contraction
-- statement:
--   Let $I$ be a nonempty finite basis of cardinality $d$, let $U$ be a unitary on this register, and let $|\alpha\rangle$ have unit norm. Define $|\phi\rangle=d^{-1/2}\sum_i|i,i\rangle$ and $|\phi(U)\rangle=(U^\dagger\otimes I)|\phi\rangle$. Then
--
--   $$ (\langle\phi(U)|_{12}\otimes I_3)(|\alpha\rangle_1\otimes|\phi\rangle_{23})=d^{-1}U|\alpha\rangle_3. $$
--
--   The resource on registers $2,3$ is unrotated. This identity is the general gate-teleportation contraction, with its branch scale unchanged.
-- source:
--   An introduction to measurement based quantum computation, arXiv:quant-ph/0508124v2, PDF p. 3, Lemma 2: rotated maximally entangled contraction

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P52

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Intakenext100.P52

open QAlgorithms.Papers.Independent.Information100.P21 (Vec)

open QAlgorithms.Papers.Independent.Gap20.P01 (applyRect)

/-- Lemma 2, PDF p.3: unrotated resource on 23 and U† on measured ket 12;
the surviving gate is U, with no transpose. -/
theorem rotated_entangled_contraction {I : Type*} [Fintype I] [Nonempty I] [DecidableEq I]
    (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ)
    (alpha : Vec I) (halpha : IsState alpha) :
    teleportContraction alpha (finiteMaxEntangled I) (rotatedEntangledKet U) =
      ((Fintype.card I : ℂ)⁻¹) • act U alpha := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P52

end
