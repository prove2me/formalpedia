-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_toricGenerator_mem_binaryCSSCheckSet
-- name    : QEC.Coding.PeriodicCubical4.toricGenerator_mem_binaryCSSCheckSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:14:47.670455+00:00
-- url     : https://prove2.me/theorems/aefb5b8b-38e9-4d5a-8ce5-d8243e4785c3
-- title:
--   Periodic Cubical4: toric Generator mem binary CSSCheck Set
-- statement:
--   The Periodic Cubical4 construction uses the toric Generator mem binary CSSCheck Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/LogicalSectors.lean#L406-L421
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/LogicalSectors.lean#L406-L421

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Hamiltonian
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_LogicalSectors
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic

theorem QEC.Coding.PeriodicCubical4.toricGenerator_mem_binaryCSSCheckSet {L : Nat} [NeZero L] [Fact (1 < L)]
    (j : Sum (Link L) (Cube L)) :
    toricGenerator (L := L) j ∈ binaryCSSCheckSet
      (plaquetteChainComplex (L := L)).firstCoboundaryCheckCode
      (plaquetteChainComplex (L := L)).middleBoundaryCode := by sorry
