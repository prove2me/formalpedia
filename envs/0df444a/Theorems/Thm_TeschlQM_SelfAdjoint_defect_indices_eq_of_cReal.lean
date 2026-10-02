-- Prove2me | Theorems.Thm_TeschlQM_SelfAdjoint_defect_indices_eq_of_cReal
-- name    : TeschlQM.SelfAdjoint.defect_indices_eq_of_cReal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:23:45.439507+00:00
-- url     : https://prove2.me/theorems/80d38789-7ff1-4a17-8ad0-a7277f405530
-- title:
--   Theorem 2.28 — a C-real symmetric operator has equal defect indices
-- statement:
--   Let $A$ be a symmetric operator on a complex Hilbert space $\mathfrak{H}$ and let $C$ be a conjugation on $\mathfrak{H}$ such that $A$ is $C$-real, i.e. $C\mathfrak{D}(A) \subseteq \mathfrak{D}(A)$ and $AC\psi = CA\psi$ for $\psi \in \mathfrak{D}(A)$. Then the defect indices of $A$ are equal:
--   $$d_+(A) = d_-(A).$$
--   Combined with Theorem 2.26 this shows that $C$-real symmetric operators, such as real differential operators, always have self-adjoint extensions.
--
--   **Formalization Note.** A conjugation is a conjugate-linear `C : H →ₗ⋆[ℂ] H` with $C^2 = \mathbb{I}$ and $\langle C\psi, C\varphi\rangle = \langle\varphi,\psi\rangle$ (antiunitary reading of the book's definition). Equality of defect indices is the existence of a unitary from $K_+ = \operatorname{Ran}(A+\mathrm{i})^\perp$ onto $K_- = \operatorname{Ran}(A-\mathrm{i})^\perp$.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 83, Theorem 2.28

import Mathlib
import Definitions.Def_TeschlQM_Shared_IsSymmetric
import Definitions.Def_TeschlQM_SelfAdjoint_defectSpace
import Definitions.Def_TeschlQM_SelfAdjoint_IsCReal

namespace TeschlQM.SelfAdjoint

/-- Teschl, Theorem 2.28 (p. 83): if the symmetric operator `A` is `C`-real for a conjugation
`C`, then its defect indices are equal. -/
theorem defect_indices_eq_of_cReal {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →ₗ.[ℂ] H) (hA : TeschlQM.Shared.IsSymmetric A) (C : H →ₗ⋆[ℂ] H) (hC : IsConjugation C)
    (hAC : IsCReal A C) :
    HasEqualDefectIndices A := by sorry

end TeschlQM.SelfAdjoint
