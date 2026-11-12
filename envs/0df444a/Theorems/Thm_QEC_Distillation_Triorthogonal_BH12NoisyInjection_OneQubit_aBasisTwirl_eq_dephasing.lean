-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12NoisyInjection_OneQubit_aBasisTwirl_eq_dephasing
-- name    : QEC.Distillation.Triorthogonal.BH12NoisyInjection.OneQubit.aBasisTwirl_eq_dephasing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:32:32.157289+00:00
-- url     : https://prove2.me/theorems/37adaef9-8f1c-4888-902c-80aeb19e5c44
-- title:
--   One Qubit: a Basis Twirl eq dephasing
-- statement:
--   The One Qubit construction uses the a Basis Twirl eq dephasing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/NoisyInjection.lean#L501-L502
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/NoisyInjection.lean#L501-L502

import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Definitions.Def_QEC_Coding_Stabilizer_Measurement
import Definitions.Def_QEC_Distillation_Triorthogonal_NoisyInjection
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.Triorthogonal
open QEC.Distillation.Triorthogonal.BH12NoisyInjection
open Semantics
open Coding
open Coding.PauliSymplectic
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u
open QEC.Distillation.Triorthogonal.BH12NoisyInjection.OneQubit
open Semantics.Qubit
open OneQubitMagic

theorem QEC.Distillation.Triorthogonal.BH12NoisyInjection.OneQubit.aBasisTwirl_eq_dephasing : aBasisTwirl = aBasisDephasing := by sorry
