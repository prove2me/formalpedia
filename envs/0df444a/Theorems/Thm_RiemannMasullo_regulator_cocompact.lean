-- Prove2me | Theorems.Thm_RiemannMasullo_regulator_cocompact
-- name    : RiemannMasullo.regulator_cocompact
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-20T23:55:02.29318+00:00
-- url     : https://prove2.me/theorems/2299126d-0120-44f6-8abb-e087997dfdb2
-- title:
--   Compactness of logarithmic space modulo the regulator lattice
-- statement:
--   The quotient of logarithmic space by the image of the integer units is compact.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec2b.lean#L141-L142

import Mathlib
open Function NumberField Topology NumberField.Units.dirichletUnitTheorem
variable (F : Type*) [Field F] [NumberField F]

namespace RiemannMasullo

theorem regulator_cocompact : CompactSpace (logSpace F ⧸ (Units.logEmbedding F).range) := by sorry

end RiemannMasullo
