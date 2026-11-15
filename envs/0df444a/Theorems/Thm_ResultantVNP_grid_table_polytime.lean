-- Prove2me | Theorems.Thm_ResultantVNP_grid_table_polytime
-- name    : ResultantVNP.grid_table_polytime
-- status  : Proved
-- author  : @gjindal
-- created : 2026-11-14T15:44:51.053839+00:00
-- url     : https://prove2.me/theorems/e73a93df-4d4c-4c95-8d5b-80c248f0c9a0
-- title:
--   Polynomial-time Turing-machine construction of the five-state grid tensor table
-- statement:
--   The map from n, encoded in unary, to the bit string gridTableCode n is computable by a finite TM2 Turing machine in time polynomial in n. This is exactly the computational clause of Lemma 3.3. A proof must provide the finite machine, a polynomial time bound, and its output correctness; a bound on the output size alone does not suffice.
-- source:
--   Bhargav–Curticapean–Jindal–Shukla, Multivariate Resultants: Complexity and Applications to Real Feasibility, STOC 2027 paper #1103, Lemma 3.3 computational clause and Appendix A.1.

import Mathlib
import Definitions.Def_ResultantVNP_gridTableCode

theorem ResultantVNP.grid_table_polytime :
    Nonempty (Turing.TM2ComputableInPolyTime Computability.unaryEncodeNat id ResultantVNP.gridTableCode) := by sorry
