-- Prove2me | Theorems.Thm_TeschlQM_SelfAdjoint_selfAdjoint_extension_iff
-- name    : TeschlQM.SelfAdjoint.selfAdjoint_extension_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:24:51.810614+00:00
-- url     : https://prove2.me/theorems/f7ffc21b-59b7-4c03-ac3c-7cdd8040a805
-- title:
--   Theorem 2.26 — self-adjoint extensions exist iff the defect indices are equal
-- statement:
--   Let $A$ be a symmetric operator on a complex Hilbert space $\mathfrak{H}$, with defect spaces $K_\pm = \operatorname{Ran}(A \pm \mathrm{i})^\perp$ and defect indices $d_\pm(A) = \dim K_\pm$. Then $A$ has a self-adjoint extension, that is a self-adjoint $B$ with $\mathfrak{D}(A) \subseteq \mathfrak{D}(B)$ and $B = A$ on $\mathfrak{D}(A)$, if and only if
--   $$d_+(A) = d_-(A).$$
--
--   This is von Neumann's criterion. It decides whether a formal quantum-mechanical Hamiltonian given on a convenient domain can be turned into a genuine observable at all, and it is the starting point for classifying all such realizations.
--
--   **Formalization Note.** Operators are `LinearPMap`s; extension is `A ≤ B`; self-adjointness is Mathlib's `IsSelfAdjoint`. Symmetric includes a dense domain, so $A^*$ is the book's adjoint. $K_\pm$ are defined as $\operatorname{Ran}(A \pm \mathrm{i})^\perp$, not as kernels of $A \mp \mathrm{i}$ (which are trivial for symmetric $A$). Equality of the Hilbert dimensions $d_\pm$ is expressed as the existence of a unitary (surjective linear isometry) $K_+ \to K_-$. No separability of $\mathfrak{H}$ is assumed; the statement holds for every complex Hilbert space.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 82, Theorem 2.26

import Mathlib
import Definitions.Def_TeschlQM_Shared_IsSymmetric
import Definitions.Def_TeschlQM_SelfAdjoint_defectSpace

namespace TeschlQM.SelfAdjoint

/-- Teschl, Theorem 2.26, first sentence (p. 82): a symmetric operator has self-adjoint extensions
if and only if its defect indices are equal. An extension `B ⊇ A` is `A ≤ B` (`𝔇(A) ⊆ 𝔇(B)`
and `B = A` on `𝔇(A)`); equality of `d₊ = dim Ran(A + i)^⊥` and `d₋ = dim Ran(A - i)^⊥` is the
existence of a unitary between the two defect spaces. -/
theorem selfAdjoint_extension_iff {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →ₗ.[ℂ] H) (hA : TeschlQM.Shared.IsSymmetric A) :
    (∃ B : H →ₗ.[ℂ] H, A ≤ B ∧ IsSelfAdjoint B) ↔ HasEqualDefectIndices A := by sorry

end TeschlQM.SelfAdjoint
