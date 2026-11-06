-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerBasis_succ_apply
-- name    : QEC.Semantics.FiniteInstrument.tensorPowerBasis_succ_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:48:57.496033+00:00
-- url     : https://prove2.me/theorems/723ea840-0c69-4067-8627-188a91a7a878
-- title:
--   Finite Instrument: tensor Power Basis succ apply
-- statement:
--   A successor tensor-power basis vector is the literal tensor product of
--   the new factor's basis vector and the recursive tail basis vector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/Basis.lean#L49-L55
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/Basis.lean#L49-L55

import Definitions.Def_QEC_Semantics_Instruments_Selection_Selection
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_Basis
set_option autoImplicit false
universe u v
open QEC
open QEC.Semantics
noncomputable section
open QEC.Semantics.FiniteInstrument
open scoped TensorProduct
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
  [FiniteQuantumSystem H]
variable {β : Type v} [Fintype β]

theorem QEC.Semantics.FiniteInstrument.tensorPowerBasis_succ_apply (b : OrthonormalBasis β Complex H)
    (attempts : Nat) (head : β) (tail : tensorPowerHistory β attempts) :
    tensorPowerBasis b (attempts + 1) (head, tail) =
      b head ⊗ₜ[Complex] tensorPowerBasis b attempts tail := by sorry
