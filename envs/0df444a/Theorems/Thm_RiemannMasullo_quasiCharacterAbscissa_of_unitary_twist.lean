-- Prove2me | Theorems.Thm_RiemannMasullo_quasiCharacterAbscissa_of_unitary_twist
-- name    : RiemannMasullo.quasiCharacterAbscissa_of_unitary_twist
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-20T22:48:37.179613+00:00
-- url     : https://prove2.me/theorems/d47b0b43-4d48-45e8-ad2f-ab46b29d5a34
-- title:
--   The abscissa of a unitary twist
-- statement:
--   Twisting a unitary character by the complex power s of the module gives abscissa Re(s).
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/Ch03_IdelicZeta/Sec1.lean#L100-L111

import Mathlib
import Definitions.Def_RiemannMasullo_QuasiCharacterAbscissa

open RiemannMasullo Function Topology
open scoped NNReal
variable {G : Type*} [CommGroup G] [TopologicalSpace G]
variable (m : G →* ℝ≥0ˣ)
local notation "modℝ" => fun g => ((m g : ℝ≥0) : ℝ)

namespace RiemannMasullo

theorem quasiCharacterAbscissa_of_unitary_twist (hm : IsProperMap m) (hne : ∃ g, m g ≠ 1)
    (c : QuasiCharacter G) (χ : PontryaginDual G) (s : ℂ)
    (hc : ∀ g, c g = (χ g : ℂ) * (modℝ g : ℂ) ^ s) :
    quasiCharacterAbscissa m hm hne c = s.re := by sorry

end RiemannMasullo
