-- Prove2me | Theorems.Thm_RiemannMasullo_regulator_discrete
-- name    : RiemannMasullo.regulator_discrete
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-20T23:55:02.208449+00:00
-- url     : https://prove2.me/theorems/af5626c6-7d7b-49f8-95e7-01af9ecf5d62
-- title:
--   Discreteness of the unit regulator image
-- statement:
--   The image of the logarithmic embedding of the integer units of a number field is discrete.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec2b.lean#L132-L133

import Mathlib
open Function NumberField Topology NumberField.Units.dirichletUnitTheorem
variable (F : Type*) [Field F] [NumberField F]

namespace RiemannMasullo

theorem regulator_discrete : IsDiscrete (Set.range (Units.logEmbedding F)) := by sorry

end RiemannMasullo
