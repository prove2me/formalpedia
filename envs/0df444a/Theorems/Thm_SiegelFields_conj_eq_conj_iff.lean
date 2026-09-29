-- Prove2me | Theorems.Thm_SiegelFields_conj_eq_conj_iff
-- name    : SiegelFields.conj_eq_conj_iff
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T01:42:28.841859+00:00
-- url     : https://prove2.me/theorems/a5a3084c-64c4-4955-840c-37b590754b79
-- title:
--   The map $SU(2)\to SO(3)$ is two-to-one: $U$ and $W$ act alike iff $W=\pm U$
-- statement:
--   Throughout, $M_2(\mathbb C)$ is the space of complex $2\times2$ matrices, $V^\dagger$ the conjugate transpose, and a **3-vector** is a matrix in $\mathcal V=\{V\in M_2(\mathbb C): V^\dagger=V,\ \operatorname{tr}V=0\}$. Let $U,W\in SU(2)$. Then
--
--   $$\big(\forall V\in\mathcal V:\ UVU^\dagger=WVW^\dagger\big)\iff W=U\ \text{ or }\ W=-U .$$
--
--   So exactly two elements of $SU(2)$ induce each rotation of 3-vectors: $SU(2)$ is a double covering of the rotation group.
-- source:
--   W. Siegel, *Fields*, arXiv:hep-th/9912205v3 (2005), https://arxiv.org/abs/hep-th/9912205, Chapter II (Spin), Section A (Two components), §IIA3 p. 115

import Mathlib
import Definitions.Def_SiegelFields_SpinDefs

open Matrix Complex

namespace SiegelFields
theorem conj_eq_conj_iff (U W : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (hW : W ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    (∀ V : Matrix (Fin 2) (Fin 2) ℂ, IsThreeVector V → U * V * Uᴴ = W * V * Wᴴ) ↔
      W = U ∨ W = -U := by sorry
end SiegelFields
