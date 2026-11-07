-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_hammingSupport_plaquetteBoundary
-- name    : QEC.Coding.PeriodicCubical4.hammingSupport_plaquetteBoundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:34:48.571844+00:00
-- url     : https://prove2.me/theorems/654c24d4-2f96-4ed5-8740-db840d51efd3
-- title:
--   Periodic Cubical4: hamming Support plaquette Boundary
-- statement:
--   The support of one primal plaquette boundary is its incident-link set.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSyndrome.lean#L200-L210
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSyndrome.lean#L200-L210

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_LogicalSectors
import Definitions.Def_QEC_Coding_Stabilizer_Energy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.hammingSupport_plaquetteBoundary (p : Plaquette L) :
    hammingSupport (plaquetteBoundary p) = plaquetteLinks p := by sorry
