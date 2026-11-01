-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P95_unitary_pushing_converse
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P95.unitary_pushing_converse
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:44:02.130409+00:00
-- url     : https://prove2.me/theorems/eefa5ff7-7576-4886-955a-8bf780faf496
-- title:
--   The converse of unitary operator pushing
-- statement:
--   Let $T:\mathcal H_A\to\mathcal H_B$ be a nonzero linear map between finite-dimensional complex Hilbert spaces. Suppose that for every unitary $U$ on $\mathcal H_A$ there exists a unitary $W$ on $\mathcal H_B$ such that $TU=WT$. Then
--
--   $$\exists c>0:\quad T^\dagger T=cI_A.$$
--
--   Consequently $T/\sqrt c$ is an isometric tensor. The outgoing unitary may depend on the incoming unitary; injectivity of $T$ is not assumed.
-- source:
--   Holographic quantum error-correcting codes: Toy models for the bulk/boundary correspondence, arXiv:1503.06237v2, PDF p. 6, §2, converse of operator pushing

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P95

namespace QAlgorithms.Papers.Independent.Intakenext100.P95

open scoped Matrix ComplexConjugate

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- PDF p.6, converse of (2.3): a nonzero tensor intertwining every incoming
unitary with some outgoing unitary has a positive scalar Gram matrix.
The outgoing unitary is chosen after the incoming one; injectivity is a conclusion. -/
theorem unitary_pushing_converse {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (T : Matrix B A ℂ) (hT : T ≠ 0)
    (hpush : ∀ U : Matrix.unitaryGroup A ℂ, ∃ W : Matrix.unitaryGroup B ℂ,
      T * (U : Matrix A A ℂ) = (W : Matrix B B ℂ) * T) :
    ∃ c : ℝ, 0 < c ∧ Tᴴ * T = (c : ℂ) • 1 := by sorry

end

end QAlgorithms.Papers.Independent.Intakenext100.P95
