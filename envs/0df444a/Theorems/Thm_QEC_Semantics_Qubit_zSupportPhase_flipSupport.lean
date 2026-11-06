-- Prove2me | Theorems.Thm_QEC_Semantics_Qubit_zSupportPhase_flipSupport
-- name    : QEC.Semantics.Qubit.zSupportPhase_flipSupport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:19:10.057672+00:00
-- url     : https://prove2.me/theorems/d94c0d80-071c-4b4f-bac1-46b6c0dcbf6a
-- title:
--   Qubit: z Support Phase flip Support
-- statement:
--   The Qubit construction uses the z Support Phase flip Support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Qubit.lean#L587-L597
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Qubit.lean#L587-L597

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Core_Qubit
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open QEC.Semantics.Qubit
open Classical
open scoped BigOperators ComplexOrder
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
omit [Fintype ι]

theorem QEC.Semantics.Qubit.zSupportPhase_flipSupport (xSupport zSupport : Finset ι)
    (bits : Bitstring ι) :
    zSupportPhase zSupport (flipSupport xSupport bits) =
      supportPhaseSign xSupport zSupport * zSupportPhase zSupport bits := by sorry
