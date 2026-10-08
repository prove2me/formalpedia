-- Prove2me | Theorems.Thm_VBSDP_Duality_trace_mul_eq_zero
-- name    : VBSDP.Duality.trace_mul_eq_zero
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:49:44.422978+00:00
-- url     : https://prove2.me/theorems/c63300ca-3904-4ee8-8f48-457463f4bc49
-- title:
--   Zero trace pairing forces a zero product
-- statement:
--   Let $A$ and $B$ be symmetric positive semidefinite real matrices of the same size. If
--
--   $$\operatorname{Tr}(AB)=0,$$
--
--   then $AB=0$.
--
--   This statement supplies a target in the duality development.
--
--   **Formalization Note** Matrices have dimension $n\times n$, with coefficients $F_1,\ldots,F_m$ indexed in Lean from 0 and $F_0$ passed separately. Positive semidefiniteness and positive definiteness are matrix conditions; trace is the matrix trace.
-- source:
--   Vandenberghe and Boyd, Semidefinite Programming, SIAM Review 38(1) (1996), p. 65, complementary slackness parenthetical, PDF p. 17, https://doi.org/10.1137/1038003

import Mathlib

namespace VBSDP.Duality

theorem trace_mul_eq_zero {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (htr : (A * B).trace = 0) :
    A * B = 0 := by sorry

end VBSDP.Duality
