-- Prove2me | Theorems.Thm_RiemannMasullo_norm_quasiCharacter_eq_rpow_abscissa
-- name    : RiemannMasullo.norm_quasiCharacter_eq_rpow_abscissa
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-20T23:11:24.466817+00:00
-- url     : https://prove2.me/theorems/f8c69ff2-f46d-46fd-befc-2b737f0e1459
-- title:
--   The modulus of a quasi-character is the module to its abscissa
-- statement:
--   On a locally compact group with a proper nontrivial positive module, the norm of every quasi-character is the module raised to its abscissa.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/Ch03_IdelicZeta/Sec1.lean#L115-L119

import Mathlib
import Definitions.Def_RiemannMasullo_QuasiCharacterAbscissa

open RiemannMasullo Function Topology
open scoped NNReal
variable {G : Type*} [CommGroup G] [TopologicalSpace G]
variable (m : G →* ℝ≥0ˣ)
local notation "modℝ" => fun g => ((m g : ℝ≥0) : ℝ)

namespace RiemannMasullo

theorem norm_quasiCharacter_eq_rpow_abscissa [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] (hm : IsProperMap m) (hne : ∃ g, m g ≠ 1)
    (c : QuasiCharacter G) (g : G) :
    ‖c g‖ = (modℝ g) ^ quasiCharacterAbscissa m hm hne c := by sorry

end RiemannMasullo
