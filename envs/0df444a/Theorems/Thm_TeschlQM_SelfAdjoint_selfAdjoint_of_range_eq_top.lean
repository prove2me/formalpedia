-- Prove2me | Theorems.Thm_TeschlQM_SelfAdjoint_selfAdjoint_of_range_eq_top
-- name    : TeschlQM.SelfAdjoint.selfAdjoint_of_range_eq_top
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:21:04.921482+00:00
-- url     : https://prove2.me/theorems/f6abd976-7f20-4b27-92e2-8f3f6818209c
-- title:
--   Lemma 2.3 — Ran(A + z) = Ran(A + z*) = ℌ implies self-adjoint
-- statement:
--   Let $A$ be a symmetric operator on a complex Hilbert space $\mathfrak{H}$ and suppose that for one $z \in \mathbb{C}$
--   $$\operatorname{Ran}(A + z) = \operatorname{Ran}(A + z^*) = \mathfrak{H}.$$
--   Then $A$ is self-adjoint.
--
--   This is a criterion for self-adjointness that does not require computing the adjoint.
--
--   **Formalization Note.** `rangeAdd A z` is $\operatorname{Ran}(A+z)$ as a subspace; "$= \mathfrak{H}$" is `= ⊤`. The number $z$ is arbitrary complex, as in the book (real $z$ allowed).
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 63, Lemma 2.3

import Mathlib
import Definitions.Def_TeschlQM_Shared_IsSymmetric
import Definitions.Def_TeschlQM_SelfAdjoint_addScalar

namespace TeschlQM.SelfAdjoint

open ComplexConjugate

/-- Teschl, Lemma 2.3 (p. 63): if `A` is symmetric and `Ran(A + z) = Ran(A + z*) = ℌ` for one
`z ∈ ℂ`, then `A` is self-adjoint. -/
theorem selfAdjoint_of_range_eq_top {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →ₗ.[ℂ] H) (hA : TeschlQM.Shared.IsSymmetric A) (z : ℂ)
    (hz : rangeAdd A z = ⊤) (hz' : rangeAdd A (conj z) = ⊤) :
    IsSelfAdjoint A := by sorry

end TeschlQM.SelfAdjoint
