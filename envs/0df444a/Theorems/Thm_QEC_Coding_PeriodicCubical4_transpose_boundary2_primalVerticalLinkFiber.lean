-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_transpose_boundary2_primalVerticalLinkFiber
-- name    : QEC.Coding.PeriodicCubical4.transpose_boundary2_primalVerticalLinkFiber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:41:22.872208+00:00
-- url     : https://prove2.me/theorems/24a15742-b9d2-4659-9145-f86e4ef64300
-- title:
--   Periodic Cubical4: transpose boundary2 primal Vertical Link Fiber
-- statement:
--   The coboundary of an `x`-link fiber is the difference of its two adjacent
--   dual membrane slices.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L749-L777
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L749-L777

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.transpose_boundary2_primalVerticalLinkFiber (x y : ZMod L) :
    wordLinearMapTranspose boundary2 (primalVerticalLinkFiber x y) =
      dualXYMembrane x y + dualXYMembrane x (y - 1) := by sorry
