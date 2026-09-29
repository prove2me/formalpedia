-- Prove2me | Theorems.Thm_SiegelFields_neg_two_det_eq_trace_sq
-- name    : SiegelFields.neg_two_det_eq_trace_sq
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T00:34:04.906458+00:00
-- url     : https://prove2.me/theorems/9836dbf3-9a7f-4226-8350-a015644beed1
-- title:
--   $-2\det M=\operatorname{tr}(M^2)-(\operatorname{tr}M)^2$ for $2\times2$ matrices
-- statement:
--   For every complex $2\times2$ matrix $M$,
--
--   $$-2\det M=\operatorname{tr}(M^2)-(\operatorname{tr}M)^2 .$$
--
--   This is the quadratic-order expansion of $\det(I+M)=e^{\operatorname{tr}\ln(I+M)}$; it expresses the determinant of a $2\times2$ matrix through traces and underlies the definition of the norm of a 3-vector.
-- source:
--   W. Siegel, *Fields*, arXiv:hep-th/9912205v3 (2005), https://arxiv.org/abs/hep-th/9912205, Chapter II (Spin), Section A (Two components), §IIA1 p. 111

import Mathlib
import Definitions.Def_SiegelFields_SpinDefs

open Matrix Complex

namespace SiegelFields
theorem neg_two_det_eq_trace_sq (M : Matrix (Fin 2) (Fin 2) ℂ) :
    -2 * M.det = trace (M * M) - (trace M) ^ 2 := by sorry
end SiegelFields
