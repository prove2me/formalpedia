-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P30_unital_transpose_unitary_equivalence
-- name    : QAlgorithms.Papers.Independent.Information100.P30.unital_transpose_unitary_equivalence
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:21:13.424312+00:00
-- url     : https://prove2.me/theorems/28f55a86-ee53-4aeb-9eb0-5b3fbe0e409f
-- title:
--   Unital transpose equivalence by unitary channels
-- statement:
--   Let $\Upsilon$ be a complex-linear CPTP qubit map with $\Upsilon(I)=I$. There exist unitary qubit matrices $L,R$ such that, writing $\mathcal U_W(X)=WXW^\dagger$,
--
--   $$\Upsilon^{\mathsf T}=\mathcal U_L\circ\Upsilon\circ\mathcal U_R.$$
--
--   The transpose is the channel transpose in the fixed computational basis. This structural result supplies unitary witnesses for the unital case; a canonical decomposition is not an extra hypothesis.
-- source:
--   Feasibility Ordering of Entanglement-Source Placement for Qubit Channels, arXiv:2609.18803v1, PDF p. 3, §III, Eq.(26)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P30

noncomputable section

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Information100.P30

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Unnumbered structural result (PDF p.3, Eq.(26), reiterated p.5, §VI):
a unital qubit channel is equivalent to its transpose by unitary channels. -/
theorem unital_transpose_unitary_equivalence (F : MatrixMap Bool Bool)
    (hF : IsQubitChannel F) (hunital : F 1 = 1) :
    ∃ L R : Matrix.unitaryGroup Bool ℂ, ∀ X : Matrix Bool Bool ℂ,
      channelTranspose F X = conjSuperop (L : Matrix Bool Bool ℂ)
        (F (conjSuperop (R : Matrix Bool Bool ℂ) X)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P30

end
