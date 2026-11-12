-- Prove2me | Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_exists_finite_subunit_gamma_selector
-- name    : QEC.Distillation.HH18.HH18SublogarithmicEntropy.exists_finite_subunit_gamma_selector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:44:24.075877+00:00
-- url     : https://prove2.me/theorems/90d32af3-6c77-4515-9da7-74a1ff2817e4
-- title:
--   HH18 Sublogarithmic Entropy: exists finite subunit gamma selector
-- statement:
--   For every positive tolerance, select a rational slope and a concrete
--   natural HH18 sequence whose finite count ratio is close to the real source
--   infimum and is strictly below `1339 / 1500`, hence below one.  The p0 witness
--   appears only through the already-derived strict upper bound on the infimum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/ParameterSelection.lean#L923-L1051
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Sublogarithmic/ParameterSelection.lean#L923-L1051

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_Entropy
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_ParameterSequence
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_BinomialTailAsymptotics
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_ParameterSelection
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Coding.PuncturedReedMuller
open Coding.ReedMuller
open Filter Topology

theorem QEC.Distillation.HH18.HH18SublogarithmicEntropy.exists_finite_subunit_gamma_selector (eta : ℝ) (heta : 0 < eta) :
    ∃ q : ℚ, ∃ A D j : Nat,
      (1 / 6 : ℚ) < q ∧ q < (1 / 3 : ℚ) ∧
        0 < A ∧ 0 < D ∧ 3 * A < D ∧ 0 < j ∧ q = (A : ℚ) / D ∧
        let r := parameterR D j
        let w := parameterW A j
        let m := parameterM D j
        let n := parameterLength A D j
        let k := parameterDimension A D j
        let d := parameterDistance A D j
        Admissible w r m ∧
          (w : ℚ) = 3 * (r : ℚ) * q ∧
          parameterGamma A D j = Real.log ((n : ℝ) / k) / Real.log d ∧
          |parameterGamma A D j - hh18GammaInf| < eta ∧
          parameterGamma A D j < (1339 / 1500 : ℝ) ∧
          parameterGamma A D j < 1 := by sorry
