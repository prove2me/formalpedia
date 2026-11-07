-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_dualXLogical_in_normalizer
-- name    : QEC.Coding.PeriodicCubical4.dualXLogical_in_normalizer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:33:13.851192+00:00
-- url     : https://prove2.me/theorems/1da7eeb6-823c-421f-98f8-2bd5c8a8887a
-- title:
--   Periodic Cubical4: dual XLogical in normalizer
-- statement:
--   The dual membrane Pauli commutes with every selected toric generator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/LogicalSectors.lean#L385-L404
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/LogicalSectors.lean#L385-L404

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Hamiltonian
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_LogicalSectors
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic

theorem QEC.Coding.PeriodicCubical4.dualXLogical_in_normalizer {L : Nat} [NeZero L] [Fact (1 < L)]
    (x y : ZMod L) :
    InStabilizerNormalizer (toricGenerator (L := L)) (dualXLogical x y) := by sorry
