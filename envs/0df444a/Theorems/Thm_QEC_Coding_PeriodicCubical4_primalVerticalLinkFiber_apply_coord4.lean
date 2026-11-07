-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_primalVerticalLinkFiber_apply_coord4
-- name    : QEC.Coding.PeriodicCubical4.primalVerticalLinkFiber_apply_coord4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:26:51.194573+00:00
-- url     : https://prove2.me/theorems/a19c7545-0ad9-4703-a254-a8e012c0e593
-- title:
--   Periodic Cubical4: primal Vertical Link Fiber apply coord4
-- statement:
--   The Periodic Cubical4 construction uses the primal Vertical Link Fiber apply coord4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L691-L713
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L691-L713

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.primalVerticalLinkFiber_apply_coord4
    (x₀ y₀ x y z w : ZMod L) (a : Axis) :
    primalVerticalLinkFiber x₀ y₀ (coord4 x y z w, a) =
      if a = .x ∧ x = x₀ ∧ y = y₀ then 1 else 0 := by sorry
