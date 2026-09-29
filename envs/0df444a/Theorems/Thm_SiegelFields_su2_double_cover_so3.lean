-- Prove2me | Theorems.Thm_SiegelFields_su2_double_cover_so3
-- name    : SiegelFields.su2_double_cover_so3
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T02:03:32.121128+00:00
-- url     : https://prove2.me/theorems/1955eca4-6ce1-431d-b742-b974d3474c1f
-- title:
--   $SU(2)$ is a double covering of $SO(3)$
-- statement:
--   For $U\in M_2(\mathbb C)$ let $R(U)$ be the real $3\times3$ matrix $R(U)_{ij}=\operatorname{Re}\operatorname{tr}(E_iUE_jU^\dagger)$, the matrix of $V\mapsto UVU^\dagger$ on traceless hermitian matrices in the basis $E_i$ of §IIA1. Then:
--
--   1. $R(U)\in SO(3)$ for every $U\in SU(2)$;
--   2. $R(UW)=R(U)R(W)$ for all $U,W\in SU(2)$;
--   3. every $R\in SO(3)$ equals $R(U)$ for some $U\in SU(2)$;
--   4. for $U,W\in SU(2)$, $R(U)=R(W)$ if and only if $W=\pm U$.
--
--   $$R:\ SU(2)\twoheadrightarrow SO(3)\ \text{ is a surjective homomorphism with } R(U)=R(W)\iff W=\pm U .$$
--
--   This is the statement that $SU(2)$ is the double covering group of the rotation group $SO(3)$, which Siegel uses to introduce spinors.
--
--   **Formalization Note** $SU(2)$ and $SO(3)$ are Mathlib's `Matrix.specialUnitaryGroup (Fin 2) ℂ` and `Matrix.specialOrthogonalGroup (Fin 3) ℝ`. Surjectivity (item 3) is implicit in the book's phrase “double covering” rather than argued there; it is included because a covering is by definition onto.
-- source:
--   W. Siegel, *Fields*, arXiv:hep-th/9912205v3 (2005), https://arxiv.org/abs/hep-th/9912205, Chapter II (Spin), Section A (Two components), §IIA2–IIA3 pp. 114–115 (see also §IC5 pp. 107–108)

import Mathlib
import Definitions.Def_SiegelFields_SpinDefs

open Matrix Complex

namespace SiegelFields
theorem su2_double_cover_so3 :
    (∀ U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ,
      rotationOf U ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) ∧
    (∀ U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ, ∀ W ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ,
      rotationOf (U * W) = rotationOf U * rotationOf W) ∧
    (∀ R ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∃ U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ, rotationOf U = R) ∧
    (∀ U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ, ∀ W ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ,
      rotationOf U = rotationOf W ↔ W = U ∨ W = -U) := by sorry
end SiegelFields
