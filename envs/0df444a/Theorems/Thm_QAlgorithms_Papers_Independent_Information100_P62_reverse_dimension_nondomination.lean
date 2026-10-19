-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_reverse_dimension_nondomination
-- name    : QAlgorithms.Papers.Independent.Information100.P62.reverse_dimension_nondomination
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T21:41:51.097987+00:00
-- url     : https://prove2.me/theorems/cba921da-71ac-4597-a3ca-137d88753e4e
-- title:
--   Example 4.3: reverse-dimensional counterexample
-- statement:
--   Let $\Phi:M_3(\mathbb C)\to M_4(\mathbb C)$ have Kraus operators $E_0=|0\rangle\langle0|+|1\rangle\langle1|/\sqrt2$ and $E_1=|2\rangle\langle1|/\sqrt2+|3\rangle\langle2|$. Then $\Phi$ is a channel and
--   $$\max\mathcal T(\Phi)=\{M_2(\mathbb C),\mathbb C^3\}.$$
--   It has no dominating transmittable algebra. This reverses the dimensions of Example 4.2.
-- source:
--   Transmitting algebras through quantum channels, arXiv:2609.40054v1, PDF p. 30, Example 4.3: reverse-dimensional counterexample

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62

namespace QAlgorithms.Papers.Independent.Information100.P62

noncomputable section

open scoped ComplexConjugate Matrix ComplexOrder

open Finset

attribute [local instance] Classical.propDecidable

variable {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]

variable [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]

/-- arXiv:2609.40054v1, PDF pp.30, 31, Example 4.3: reverse-dimensional counterexample. -/
theorem reverse_dimension_nondomination :
    IsChannel example43 ∧ maximals example43 = {quantum 2, classical 3} ∧ ¬ HasDominating example43 := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P62
