-- Prove2me | Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_exists_selected_code_bridge
-- name    : QEC.Distillation.HH18.HH18SublogarithmicEntropy.exists_selected_code_bridge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T21:32:39.29873+00:00
-- url     : https://prove2.me/theorems/e80610da-9d1b-4bdb-832f-b0233799e24a
-- title:
--   HH18 Sublogarithmic Entropy: exists selected code bridge
-- statement:
--   Every finite Gamma-selector witness instantiates the actual #759 encoded
--   code with its exact n, k, and d, together with the two correctly oriented
--   simultaneous transversal actions.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/SelectedCode.lean#L109-L144
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/SelectedCode.lean#L109-L144

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_ParameterSelection
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PuncturedReedMuller
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_SelectedCode
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Coding
open Coding.PuncturedReedMuller
open QEC.Distillation.HH18PuncturedReedMuller

theorem QEC.Distillation.HH18.HH18SublogarithmicEntropy.exists_selected_code_bridge (eta : ℝ) (heta : 0 < eta) :
    ∃ q : ℚ, ∃ A D j : Nat,
      (1 / 6 : ℚ) < q ∧ q < (1 / 3 : ℚ) ∧
        0 < A ∧ 0 < D ∧ 3 * A < D ∧ 0 < j ∧ q = (A : ℚ) / D ∧
        let r := parameterR D j
        let w := parameterW A j
        let m := parameterM D j
        let n := parameterLength A D j
        let k := parameterDimension A D j
        let d := parameterDistance A D j
        ∃ h : Admissible w r m,
          (w : ℚ) = 3 * (r : ℚ) * q ∧
            Length (ZMod 2) (PhysicalSite m w) = n ∧
              Length (ZMod 2) (PhysicalSite m w) -
                  Dimension (xCode w r m) - Dimension (zCode w r m) = k ∧
                Module.finrank Complex (cssCode h).stabilizer.code.carrier = 2 ^ k ∧
                  StabilizerCode.SemanticStabilizerDistance
                    (sourceValidStabilizer h) d ∧
                    (encodedCode h).ImplementsLogicalGate
                      (physicalT w m) (logicalTInv w m) ∧
                    (encodedCode h).ImplementsLogicalGate
                      (physicalTInv w m) (logicalT w m) := by sorry
