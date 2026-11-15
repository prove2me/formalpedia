-- Prove2me | Theorems.Thm_ResultantVNP_grid_permanent_identity
-- name    : ResultantVNP.grid_permanent_identity
-- status  : Proved
-- author  : @gjindal
-- created : 2026-11-14T15:43:44.98517+00:00
-- url     : https://prove2.me/theorems/c2ae262c-afdf-4488-8a20-946e1c523dbc
-- title:
--   The permanent equals the five-state grid assignment polynomial
-- statement:
--   For every natural number n, the grid assignment sum of the five-state tensor gridTensor n is exactly the permanent of the generic n by n matrix, as a polynomial over the integers. This proves the polynomial identity in Lemma 3.3, independently of the separate Turing-machine running-time clause.
-- source:
--   Bhargav–Curticapean–Jindal–Shukla, Multivariate Resultants: Complexity and Applications to Real Feasibility, STOC 2027 paper #1103, Lemma 3.3 and Appendix A.1.

import Mathlib
import Definitions.Def_ResultantVNP_gridTensor

theorem ResultantVNP.grid_permanent_identity (n : ℕ) :
    ResultantVNP.gridSum (fun α : ResultantVNP.GridIdx (ResultantVNP.gridSide n) => α.1)
      (ResultantVNP.gridTensor n) =
      (Matrix.of fun i j : Fin n => (MvPolynomial.X (i,j) : MvPolynomial (Fin n × Fin n) ℤ)).permanent := by sorry
