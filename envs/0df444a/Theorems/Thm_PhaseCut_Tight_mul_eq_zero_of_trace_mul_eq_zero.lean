-- Prove2me | Theorems.Thm_PhaseCut_Tight_mul_eq_zero_of_trace_mul_eq_zero
-- name    : PhaseCut.Tight.mul_eq_zero_of_trace_mul_eq_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:40:57.811983+00:00
-- url     : https://prove2.me/theorems/f681c2e0-18ba-453d-b933-a905956e26e3
-- title:
--   Proof of Proposition 4.2, p. 12 — for U, M ⪰ 0, Tr(UM) = 0 implies UM = 0
-- statement:
--   Let $U$ and $M$ be $m\times m$ Hermitian positive semidefinite complex matrices. If
--
--   $$\operatorname{Tr}(UM)=0,$$
--
--   then $UM=0$.
--
--   In the proof of Proposition 4.2 this turns the PhaseCutMod constraint $\operatorname{Tr}(MU)=0$ into the matrix equation $MU=0$, from which the range condition $AA^\dagger\operatorname{diag}(b)U\operatorname{diag}(b)=\operatorname{diag}(b)U\operatorname{diag}(b)$ follows.
--
--   **Formalization Note** Positive semidefiniteness is Mathlib's `Matrix.PosSemidef`, which includes Hermitianity; the trace hypothesis is an equation in $\mathbb C$.
-- source:
--   Waldspurger, d'Aspremont & Mallat, arXiv:1206.0102v3, proof of Proposition 4.2, p. 12

import Mathlib
import Definitions.Def_PhaseCut_Tight_Defs

namespace PhaseCut.Tight

open Matrix
open scoped ComplexOrder

/-- Proof of Proposition 4.2, p. 12: for positive semidefinite Hermitian `U, M`,
`Tr(UM) = 0` forces `UM = 0`. -/
theorem mul_eq_zero_of_trace_mul_eq_zero {m : ℕ} (U M : Matrix (Fin m) (Fin m) ℂ)
    (hU : U.PosSemidef) (hM : M.PosSemidef) (h : (U * M).trace = 0) :
    U * M = 0 := by sorry

end PhaseCut.Tight
