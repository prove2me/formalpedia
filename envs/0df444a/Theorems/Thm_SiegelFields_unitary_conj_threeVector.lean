-- Prove2me | Theorems.Thm_SiegelFields_unitary_conj_threeVector
-- name    : SiegelFields.unitary_conj_threeVector
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T01:26:30.944652+00:00
-- url     : https://prove2.me/theorems/8bac1084-5858-470a-a59c-07f1c5c96267
-- title:
--   Rotations $V'=UVU^\dagger$ preserve 3-vectors and their norm
-- statement:
--   Throughout, $M_2(\mathbb C)$ is the space of complex $2\times2$ matrices, $V^\dagger$ the conjugate transpose, and a **3-vector** is a matrix in $\mathcal V=\{V\in M_2(\mathbb C): V^\dagger=V,\ \operatorname{tr}V=0\}$. If $U$ is a unitary $2\times2$ matrix ($U^\dagger=U^{-1}$) and $V\in\mathcal V$, then $V'=UVU^\dagger$ is again a 3-vector and
--
--   $$\det(UVU^\dagger)=\det V ,$$
--
--   so the transformation preserves the norm $|V|^2=-2\det V$ (and hence the inner product).
-- source:
--   W. Siegel, *Fields*, arXiv:hep-th/9912205v3 (2005), https://arxiv.org/abs/hep-th/9912205, Chapter II (Spin), Section A (Two components), §IIA2 p. 114

import Mathlib
import Definitions.Def_SiegelFields_SpinDefs

open Matrix Complex

namespace SiegelFields
theorem unitary_conj_threeVector (U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) (V : Matrix (Fin 2) (Fin 2) ℂ)
    (hV : IsThreeVector V) :
    IsThreeVector (U * V * Uᴴ) ∧ (U * V * Uᴴ).det = V.det := by sorry
end SiegelFields
