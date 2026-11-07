-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_transpose_boundary2_primalHorizontalLinkFiber
-- name    : QEC.Coding.PeriodicCubical4.transpose_boundary2_primalHorizontalLinkFiber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:41:13.521947+00:00
-- url     : https://prove2.me/theorems/ab122359-0322-44b4-b258-13e6178e9cb3
-- title:
--   Periodic Cubical4: transpose boundary2 primal Horizontal Link Fiber
-- statement:
--   The coboundary of a `y`-link fiber is the difference of its two adjacent
--   dual membrane slices.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L717-L745
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/EnergyBarrierLowerBound.lean#L717-L745

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.transpose_boundary2_primalHorizontalLinkFiber (x y : ZMod L) :
    wordLinearMapTranspose boundary2 (primalHorizontalLinkFiber x y) =
      dualXYMembrane x y + dualXYMembrane (x - 1) y := by sorry
