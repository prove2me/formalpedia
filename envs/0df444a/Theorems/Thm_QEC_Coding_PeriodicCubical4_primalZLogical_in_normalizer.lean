-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_primalZLogical_in_normalizer
-- name    : QEC.Coding.PeriodicCubical4.primalZLogical_in_normalizer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:32:59.688142+00:00
-- url     : https://prove2.me/theorems/635cdf9c-7c92-45e2-9523-03513618645e
-- title:
--   Periodic Cubical4: primal ZLogical in normalizer
-- statement:
--   The primal membrane Pauli commutes with every selected toric generator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/LogicalSectors.lean#L366-L382
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/LogicalSectors.lean#L366-L382

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Hamiltonian
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_LogicalSectors
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic

theorem QEC.Coding.PeriodicCubical4.primalZLogical_in_normalizer {L : Nat} [NeZero L] [Fact (1 < L)]
    (z w : ZMod L) :
    InStabilizerNormalizer (toricGenerator (L := L)) (primalZLogical z w) := by sorry
