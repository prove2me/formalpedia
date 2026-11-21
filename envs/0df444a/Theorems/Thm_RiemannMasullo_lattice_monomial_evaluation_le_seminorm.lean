-- Prove2me | Theorems.Thm_RiemannMasullo_lattice_monomial_evaluation_le_seminorm
-- name    : RiemannMasullo.lattice_monomial_evaluation_le_seminorm
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T03:16:47.630872+00:00
-- url     : https://prove2.me/theorems/bcae2004-4fe7-4589-801b-35380620b47b
-- title:
--   Lattice monomial evaluations are controlled by the elementary Schwartz seminorm
-- statement:
--   Evaluating a lattice Schwartz function at any integer point after multiplication by a coordinate monomial is bounded by the corresponding defining seminorm.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L604-L606

import Definitions.Def_RiemannMasullo_ElementarySchwartzTopology
import Mathlib
open RiemannMasullo

namespace RiemannMasullo
theorem lattice_monomial_evaluation_le_seminorm (r : ℕ) (f : ElementarySchwartz 0 0 r PUnit) (d : Fin r → ℕ) (a : Fin r → ℤ) :
    (∏ i, |(a i:ℝ)|^d i)*‖f (0,0,a,PUnit.unit)‖ ≤ elementarySchwartzSeminorm (0,0,0,d) f := by sorry
end RiemannMasullo
