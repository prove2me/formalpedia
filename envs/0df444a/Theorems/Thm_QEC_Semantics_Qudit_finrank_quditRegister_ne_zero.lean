-- Prove2me | Theorems.Thm_QEC_Semantics_Qudit_finrank_quditRegister_ne_zero
-- name    : QEC.Semantics.Qudit.finrank_quditRegister_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:20:09.318201+00:00
-- url     : https://prove2.me/theorems/eb8f8795-2354-427f-ab8c-d02a20cff885
-- title:
--   Qudit: finrank qudit Register ne zero
-- statement:
--   A canonical finite qudit register has nonzero finite complex dimension.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L44-L49
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L44-L49

import Definitions.Def_QEC_Semantics_Channels_Core
import Mathlib.Analysis.InnerProductSpace.PiL2
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Semantics.Qudit

theorem QEC.Semantics.Qudit.finrank_quditRegister_ne_zero {ι : Type u} [Fintype ι]
    (q : ι → Nat) (hq : ∀ i, 0 < q i) :
    (Module.finrank Complex (QuditRegister q) : Complex) ≠ 0 := by sorry
