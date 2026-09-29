-- Prove2me | Theorems.Thm_SiegelFields_reality_conditions
-- name    : SiegelFields.reality_conditions
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T01:26:57.791703+00:00
-- url     : https://prove2.me/theorems/2a6a79c6-9b05-4e14-bb31-8570676ff18a
-- title:
--   Reality conditions: $V^*=-CVC$ for 3-vectors and $U^*=CUC$ for $U\in SU(2)$
-- statement:
--   Let $C=\begin{pmatrix}0&-i\\ i&0\end{pmatrix}$ and let $X^*$ denote the entrywise complex conjugate.
--
--   1. If $V^\dagger=V$ and $\operatorname{tr}V=0$, then $V^*=-CVC$.
--   2. If $U^\dagger=U^{-1}$ and $\det U=1$ (i.e. $U\in SU(2)$), then $U^*=CUC$.
--
--   These express hermiticity of 3-vectors and special unitarity of rotations as reality conditions.
-- source:
--   W. Siegel, *Fields*, arXiv:hep-th/9912205v3 (2005), https://arxiv.org/abs/hep-th/9912205, Chapter II (Spin), Section A (Two components), §IIA2 pp. 114–115

import Mathlib
import Definitions.Def_SiegelFields_SpinDefs

open Matrix Complex

namespace SiegelFields
theorem reality_conditions :
    (∀ V : Matrix (Fin 2) (Fin 2) ℂ, IsThreeVector V → V.map star = -(matC * V * matC)) ∧
    (∀ U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ, U.map star = matC * U * matC) := by sorry
end SiegelFields
