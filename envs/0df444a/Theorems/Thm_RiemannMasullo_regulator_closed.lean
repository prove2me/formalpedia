-- Prove2me | Theorems.Thm_RiemannMasullo_regulator_closed
-- name    : RiemannMasullo.regulator_closed
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-20T23:55:04.336727+00:00
-- url     : https://prove2.me/theorems/af23316f-ce5c-46b3-b5e1-2c9a3f6c6aff
-- title:
--   Closedness of the unit regulator image
-- statement:
--   The image of the logarithmic embedding of the integer units is closed in logarithmic space.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec2b.lean#L136-L137

import Mathlib
open Function NumberField Topology NumberField.Units.dirichletUnitTheorem
variable (F : Type*) [Field F] [NumberField F]

namespace RiemannMasullo

theorem regulator_closed : IsClosed (Set.range (Units.logEmbedding F)) := by sorry

end RiemannMasullo
