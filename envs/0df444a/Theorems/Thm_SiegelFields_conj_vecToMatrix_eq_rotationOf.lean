-- Prove2me | Theorems.Thm_SiegelFields_conj_vecToMatrix_eq_rotationOf
-- name    : SiegelFields.conj_vecToMatrix_eq_rotationOf
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T01:54:34.832807+00:00
-- url     : https://prove2.me/theorems/c6a1863d-9595-4c41-87f7-27756558dcc4
-- title:
--   The matrix $R(U)$ represents $V\mapsto UVU^\dagger$ in the book's basis
-- statement:
--   Let $U$ be a unitary $2\times2$ matrix and $R(U)_{ij}=\operatorname{Re}\operatorname{tr}(E_iUE_jU^\dagger)$. For every $v\in\mathbb R^3$,
--
--   $$U\,V(v)\,U^\dagger=V\big(R(U)\,v\big),$$
--
--   where $R(U)v$ is the matrix–vector product. Thus $R(U)$ is the $3\times3$ matrix of the rotation $V'=UVU^\dagger$ in components.
-- source:
--   W. Siegel, *Fields*, arXiv:hep-th/9912205v3 (2005), https://arxiv.org/abs/hep-th/9912205, Chapter II (Spin), Section A (Two components), §IIA2 p. 114 (with the basis of §IIA1 p. 111)

import Mathlib
import Definitions.Def_SiegelFields_SpinDefs

open Matrix Complex

namespace SiegelFields
theorem conj_vecToMatrix_eq_rotationOf (U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) (v : Fin 3 → ℝ) :
    U * vecToMatrix v * Uᴴ = vecToMatrix (rotationOf U *ᵥ v) := by sorry
end SiegelFields
