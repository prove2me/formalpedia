-- Prove2me | Theorems.Thm_TeschlQM_SelfAdjoint_cayley_transform_bijective
-- name    : TeschlQM.SelfAdjoint.cayley_transform_bijective
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:22:51.160422+00:00
-- url     : https://prove2.me/theorems/ffb7a784-f66b-4bf7-829e-e527d1ec9305
-- title:
--   Theorem 2.25 — the Cayley transform is a bijection onto isometries with Ran(1 − V) dense
-- statement:
--   Let $\mathfrak{H}$ be a complex Hilbert space. For a symmetric operator $A$ let $V = (A - \mathrm{i})(A + \mathrm{i})^{-1}$, defined on $\mathfrak{D}(V) = \operatorname{Ran}(A + \mathrm{i})$, be its Cayley transform. The Cayley transform is a bijection
--   $$\{A \text{ symmetric}\} \longrightarrow \{V \text{ isometric} \mid \operatorname{Ran}(1 - V) \text{ dense}\}.$$
--   Explicitly: every symmetric $A$ has a Cayley transform, it is unique, isometric ($\|V\varphi\| = \|\varphi\|$ on $\mathfrak{D}(V)$), and $\operatorname{Ran}(1-V)$ is dense; two symmetric operators with the same Cayley transform are equal; and every isometric $V$ with $\operatorname{Ran}(1 - V)$ dense is the Cayley transform of some symmetric $A$.
--
--   The Cayley transform converts questions about self-adjoint extensions of $A$ into questions about unitary extensions of $V$.
--
--   **Formalization Note.** "$V$ is the Cayley transform of $A$" is the relation `IsCayleyTransform A V` ($\mathfrak{D}(V) = \operatorname{Ran}(A+\mathrm{i})$ and $V(A+\mathrm{i})\psi = (A-\mathrm{i})\psi$). The bijection is stated as its four constituent facts: existence with the stated properties, uniqueness of $V$ given $A$, injectivity, and surjectivity.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 81, Theorem 2.25

import Mathlib
import Definitions.Def_TeschlQM_Shared_IsSymmetric
import Definitions.Def_TeschlQM_SelfAdjoint_IsCayleyTransform

namespace TeschlQM.SelfAdjoint

/-- Teschl, Theorem 2.25 (p. 81): the Cayley transform `A ↦ V = (A - i)(A + i)⁻¹` is a bijection
from the symmetric operators onto the isometric operators `V` with `Ran(1 - V)` dense:
every symmetric `A` has a Cayley transform, unique, isometric and with `Ran(1 - V)` dense;
distinct symmetric operators have distinct Cayley transforms; and every isometric `V` with
`Ran(1 - V)` dense is the Cayley transform of a symmetric operator. -/
theorem cayley_transform_bijective {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :
    (∀ A : H →ₗ.[ℂ] H, TeschlQM.Shared.IsSymmetric A →
      ∃ V : H →ₗ.[ℂ] H, IsCayleyTransform A V ∧ IsIsometric V ∧
        Dense (rangeOneSub V : Set H)) ∧
    (∀ A V W : H →ₗ.[ℂ] H, TeschlQM.Shared.IsSymmetric A → IsCayleyTransform A V → IsCayleyTransform A W →
      V = W) ∧
    (∀ A B V : H →ₗ.[ℂ] H, TeschlQM.Shared.IsSymmetric A → TeschlQM.Shared.IsSymmetric B → IsCayleyTransform A V →
      IsCayleyTransform B V → A = B) ∧
    (∀ V : H →ₗ.[ℂ] H, IsIsometric V → Dense (rangeOneSub V : Set H) →
      ∃ A : H →ₗ.[ℂ] H, TeschlQM.Shared.IsSymmetric A ∧ IsCayleyTransform A V) := by sorry

end TeschlQM.SelfAdjoint
