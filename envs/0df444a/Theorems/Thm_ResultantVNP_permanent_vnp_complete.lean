-- Prove2me | Theorems.Thm_ResultantVNP_permanent_vnp_complete
-- name    : ResultantVNP.permanent_vnp_complete
-- status  : Open
-- author  : @gjindal
-- created : 2026-11-14T16:32:22.926045+00:00
-- url     : https://prove2.me/theorems/f19393bf-954a-4e16-a545-8c35e4e9ce4a
-- title:
--   Valiant completeness: the permanent is VNP-hard under p-projections
-- statement:
--   Over the complex numbers, every family in VNP is a p-projection of the generic permanent family. More precisely, for every VNP family (f_n), there is a polynomially bounded function t with t(n) at least 1 such that f_n is obtained from the permanent of a t(n)-by-t(n) matrix by substituting variables and complex constants. VNP here is the Boolean exponential-sum closure of the bounded-degree arithmetic-circuit class VP. This is the classical permanent-completeness result used to pass from the explicit permanent projection in Theorem 3.2 to VNP-hardness.
-- source:
--   The classical Valiant permanent-completeness theorem, as invoked in Section 3.1 and the proof of Theorem 3.2 of Bhargav–Curticapean–Jindal–Shukla, Multivariate Resultants: Complexity and Applications to Real Feasibility, STOC 2027 paper #1103.

import Mathlib
import Definitions.Def_ResultantVNP_IsVNPHardPProj

theorem ResultantVNP.permanent_vnp_complete :
    ResultantVNP.IsVNPHardPProj
      (fun n => (Matrix.of fun i j : Fin n =>
        (MvPolynomial.X (i,j) : MvPolynomial (Fin n × Fin n) ℂ)).permanent) 1 := by sorry
