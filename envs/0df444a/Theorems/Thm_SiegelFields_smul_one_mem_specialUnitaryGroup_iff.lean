-- Prove2me | Theorems.Thm_SiegelFields_smul_one_mem_specialUnitaryGroup_iff
-- name    : SiegelFields.smul_one_mem_specialUnitaryGroup_iff
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T01:41:00.46563+00:00
-- url     : https://prove2.me/theorems/659a3dcd-3a26-42e4-88e9-e0b87c162739
-- title:
--   The scalar matrices in $SU(2)$ are $\pm I$
-- statement:
--   For $c\in\mathbb C$, the scalar matrix $cI$ lies in $SU(2)$ if and only if $c=1$ or $c=-1$.
--
--   In the book: $\det(Ie^{i\theta})=e^{2i\theta}=1\Rightarrow e^{i\theta}=\pm1$ for $2\times2$ matrices; this is why the phase factors surviving in $SU(2)$ are only $\pm1$.
-- source:
--   W. Siegel, *Fields*, arXiv:hep-th/9912205v3 (2005), https://arxiv.org/abs/hep-th/9912205, Chapter II (Spin), Section A (Two components), §IIA3 p. 115

import Mathlib
import Definitions.Def_SiegelFields_SpinDefs

open Matrix Complex

namespace SiegelFields
theorem smul_one_mem_specialUnitaryGroup_iff (c : ℂ) :
    c • (1 : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ ↔
      c = 1 ∨ c = -1 := by sorry
end SiegelFields
