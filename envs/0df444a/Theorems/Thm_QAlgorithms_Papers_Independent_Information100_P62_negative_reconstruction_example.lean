-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_negative_reconstruction_example
-- name    : QAlgorithms.Papers.Independent.Information100.P62.negative_reconstruction_example
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T21:43:25.003304+00:00
-- url     : https://prove2.me/theorems/79ccf3af-10eb-4529-9f61-da18521ac603
-- title:
--   Unnumbered negative-multiplicity example, footnote 4
-- statement:
--   For the $7$-dimensional channel of footnote 4, with Kraus operators $E_1=|0\rangle\langle0|+|1\rangle\langle1|+|2\rangle\langle2|$, $E_2=|0\rangle\langle3|+|1\rangle\langle4|$, and $E_3=|2\rangle\langle5|+|6\rangle\langle6|$, both $M_3(\mathbb C)$ and $M_2(\mathbb C)^{\oplus2}$ are transmittable. Its data are
--   $$d_{\max}=3,\quad(c_1,c_2,c_3)=(4,2,1),\quad(N_1,N_2,N_3)=(-1,1,1).$$
--   The capacity algebra is therefore undefined. This shows that reconstruction multiplicities can be negative.
-- source:
--   Transmitting algebras through quantum channels, arXiv:2609.40054v1, PDF p. 34, Unnumbered negative-multiplicity example, footnote 4

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62

namespace QAlgorithms.Papers.Independent.Information100.P62

noncomputable section

open scoped ComplexConjugate Matrix ComplexOrder

open Finset

attribute [local instance] Classical.propDecidable

variable {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]

variable [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]

/-- arXiv:2609.40054v1, PDF pp.34, Unnumbered negative-multiplicity example, footnote 4. -/
theorem negative_reconstruction_example :
    IsChannel negativeExample ∧ Transmits negativeExample (quantum 3) ∧
    Transmits negativeExample (equalBlocks 2 2) ∧ dmax negativeExample = 3 ∧
    hybrid negativeExample 1 = 4 ∧ hybrid negativeExample 2 = 2 ∧ hybrid negativeExample 3 = 1 ∧
    multiplicity negativeExample 3 = 1 ∧ multiplicity negativeExample 2 = 1 ∧
    multiplicity negativeExample 1 = -1 ∧ capacityAlgebra negativeExample = none := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P62
