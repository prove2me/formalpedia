-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_small_dimension_nondomination
-- name    : QAlgorithms.Papers.Independent.Information100.P62.small_dimension_nondomination
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T21:30:14.825986+00:00
-- url     : https://prove2.me/theorems/abe3bc0a-6905-4955-8a3a-1f493c91eb24
-- title:
--   Main nonexistence result; Example 4.2 and (4.3)
-- statement:
--   Let $\Phi:M_4(\mathbb C)\to M_3(\mathbb C)$ have the three Kraus operators of Example 4.2: $E_1=|0\rangle\langle0|+|1\rangle\langle1|$, $E_2=(|1\rangle+|2\rangle)\langle2|/\sqrt2$, and $E_3=(|1\rangle-|2\rangle)\langle3|/\sqrt2$. Then $\Phi$ is a channel and
--   $$\max\mathcal T(\Phi)=\{M_2(\mathbb C),\mathbb C^3\},$$
--   and no transmittable algebra dominates its transmission set. This is the paper's small-dimensional nonexistence witness.
-- source:
--   Transmitting algebras through quantum channels, arXiv:2609.40054v1, PDF p. 30, Main nonexistence result; Example 4.2 and (4.3)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62

namespace QAlgorithms.Papers.Independent.Information100.P62

noncomputable section

open scoped ComplexConjugate Matrix ComplexOrder

open Finset

attribute [local instance] Classical.propDecidable

variable {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]

variable [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]

/-- arXiv:2609.40054v1, PDF pp.1, 6, 29, 30, Main nonexistence result; Example 4.2 and (4.3). -/
theorem small_dimension_nondomination :
    IsChannel example42 ∧ maximals example42 = {quantum 2, classical 3} ∧ ¬ HasDominating example42 := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P62
