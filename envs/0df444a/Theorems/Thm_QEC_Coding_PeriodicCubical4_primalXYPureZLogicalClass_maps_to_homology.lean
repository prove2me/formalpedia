-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_primalXYPureZLogicalClass_maps_to_homology
-- name    : QEC.Coding.PeriodicCubical4.primalXYPureZLogicalClass_maps_to_homology
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:46:31.660437+00:00
-- url     : https://prove2.me/theorems/ba7823cc-ffcf-4f93-858e-40592d1c11e7
-- title:
--   Periodic Cubical4: primal XYPure ZLogical Class maps to homology
-- statement:
--   The Periodic Cubical4 construction uses the primal XYPure ZLogical Class maps to homology property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/LogicalSectors.lean#L321-L326
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/LogicalSectors.lean#L321-L326

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Hamiltonian
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_LogicalSectors
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators

theorem QEC.Coding.PeriodicCubical4.primalXYPureZLogicalClass_maps_to_homology {L : Nat} [NeZero L]
    (z w : ZMod L) :
    (plaquetteChainComplex (L := L)).pureZLogicalQuotientEquivMiddleHomology
        (primalXYPureZLogicalClass z w) =
      primalXYHomologyClass z w := by sorry
