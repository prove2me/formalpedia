-- Prove2me | Theorems.Thm_TeschlQM_SelfAdjoint_selfAdjoint_maximal
-- name    : TeschlQM.SelfAdjoint.selfAdjoint_maximal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:20:31.495445+00:00
-- url     : https://prove2.me/theorems/0a0092a1-9a02-43ca-b845-5ba1a9f864ba
-- title:
--   Corollary 2.2 — self-adjoint operators are maximal
-- statement:
--   Let $A$ be a self-adjoint operator on a complex Hilbert space $\mathfrak{H}$ and let $B$ be a symmetric operator extending $A$, that is, $\mathfrak{D}(A) \subseteq \mathfrak{D}(B)$ and $B\psi = A\psi$ for $\psi \in \mathfrak{D}(A)$. Then
--   $$B = A.$$
--   So a self-adjoint operator has no proper symmetric extension; in particular an essentially self-adjoint operator has exactly one self-adjoint extension.
--
--   **Formalization Note.** Extension is the order `A ≤ B` on `LinearPMap`. Self-adjointness is Mathlib's `IsSelfAdjoint` (equality with the adjoint), and symmetry includes density of the domain.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 60, Corollary 2.2

import Mathlib
import Definitions.Def_TeschlQM_Shared_IsSymmetric

namespace TeschlQM.SelfAdjoint

/-- Teschl, Corollary 2.2 (p. 60): self-adjoint operators are maximal, i.e. a symmetric extension
`B ⊇ A` of a self-adjoint `A` equals `A`. -/
theorem selfAdjoint_maximal {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A B : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (hB : TeschlQM.Shared.IsSymmetric B) (hAB : A ≤ B) :
    B = A := by sorry

end TeschlQM.SelfAdjoint
