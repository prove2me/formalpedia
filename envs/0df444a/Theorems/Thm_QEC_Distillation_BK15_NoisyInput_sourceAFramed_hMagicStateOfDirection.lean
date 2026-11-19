-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_NoisyInput_sourceAFramed_hMagicStateOfDirection
-- name    : QEC.Distillation.BK15.NoisyInput.sourceAFramed_hMagicStateOfDirection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T01:08:05.608212+00:00
-- url     : https://prove2.me/theorems/61e30d7f-b2bf-4e30-992b-f6970dc1a99b
-- title:
--   Noisy Input: source AFramed h Magic State Of Direction
-- statement:
--   Every ideal H-orbit witness is mapped to the source `A₀` density.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/NoisyInput.lean#L668-L672
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/NoisyInput.lean#L668-L672

import Definitions.Def_QEC_Coding_Stabilizer_Measurement
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
import Definitions.Def_QEC_Distillation_Universality_HResourcePhase
import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_FifteenQubitH_NoisyInput
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK15
open QEC.Distillation.BK15.NoisyInput
open Semantics Semantics.Qubit
open OneQubitMagic
open Coding.PauliSymplectic
open scoped BigOperators TensorProduct
universe u v w
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.BK15.NoisyInput.sourceAFramed_hMagicStateOfDirection (d : HDirection) :
    sourceA0Transport.conjDensity
      ((hCanonicalizer d).conjDensity (hMagicStateOfDirection d)) = aZeroDensity := by sorry
