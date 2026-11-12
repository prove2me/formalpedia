-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthPooledYield_five_sixths_le
-- name    : QEC.Distillation.HH18Parameterized.routedDepthPooledYield_five_sixths_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:42:12.683211+00:00
-- url     : https://prove2.me/theorems/45ea0351-a154-458e-a42a-2750251f3ce3
-- title:
--   HH18 Parameterized: routed Depth Pooled Yield five sixths le
-- statement:
--   Averaging the literal finite path-survival products preserves their
--   uniform five-sixths lower bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PathYield.lean#L335-L354
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PathYield.lean#L335-L354

import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathEnvelope
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathYield
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open scoped BigOperators
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.routedDepthPooledYield_five_sixths_le {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) :
    (5 / 6 : ℝ) ≤ (routedDepthPooledYield h hdegree epsilon hsmall depth : ℝ) := by sorry
