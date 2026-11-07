-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_kraus
-- name    : QEC.Coding.PauliSymplectic.stabilizerInstrument_kraus
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:28:32.654209+00:00
-- url     : https://prove2.me/theorems/9a91d1e0-9120-4365-9275-169e3ac8ed78
-- title:
--   Pauli Symplectic: stabilizer Instrument kraus
-- statement:
--   The Pauli Symplectic construction uses the stabilizer Instrument kraus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Measurement.lean#L230-L232
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Measurement.lean#L230-L232

import Definitions.Def_QEC_Coding_Stabilizer_HermitianPauli
import Definitions.Def_QEC_Semantics_Instruments_Core
import Definitions.Def_QEC_Coding_Stabilizer_Measurement
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PauliSymplectic
open Semantics
open scoped BigOperators
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Coding.PauliSymplectic.stabilizerInstrument_kraus (P : Binary ι) :
    (stabilizerInstrument P).kraus = stabilizerKrausFamily P := by sorry

attribute [defeq] QEC.Coding.PauliSymplectic.stabilizerInstrument_kraus
