-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_primalHorizontalLinkFiber_apply_coord4
-- name    : QEC.Coding.PeriodicCubical4.primalHorizontalLinkFiber_apply_coord4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:27:04.369988+00:00
-- url     : https://prove2.me/theorems/b2570a2b-4731-4587-bb0a-6bd183a70e81
-- title:
--   Periodic Cubical4: primal Horizontal Link Fiber apply coord4
-- statement:
--   The Periodic Cubical4 construction uses the primal Horizontal Link Fiber apply coord4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L667-L689
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L667-L689

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.primalHorizontalLinkFiber_apply_coord4
    (x₀ y₀ x y z w : ZMod L) (a : Axis) :
    primalHorizontalLinkFiber x₀ y₀ (coord4 x y z w, a) =
      if a = .y ∧ x = x₀ ∧ y = y₀ then 1 else 0 := by sorry
