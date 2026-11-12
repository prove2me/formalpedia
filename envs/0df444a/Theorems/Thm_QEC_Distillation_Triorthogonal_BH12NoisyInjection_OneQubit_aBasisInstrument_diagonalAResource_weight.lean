-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12NoisyInjection_OneQubit_aBasisInstrument_diagonalAResource_weight
-- name    : QEC.Distillation.Triorthogonal.BH12NoisyInjection.OneQubit.aBasisInstrument_diagonalAResource_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:31:34.286057+00:00
-- url     : https://prove2.me/theorems/1e0bd44a-fa6c-4a18-9a84-203474a891ff
-- title:
--   One Qubit: a Basis Instrument diagonal AResource weight
-- statement:
--   The One Qubit construction uses the a Basis Instrument diagonal AResource weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/NoisyInjection.lean#L455-L474
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/NoisyInjection.lean#L455-L474

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

theorem QEC.Distillation.Triorthogonal.BH12NoisyInjection.OneQubit.aBasisInstrument_diagonalAResource_weight (p : ErrorParameter)
    (outcome : StabilizerOutcome) :
    aBasisInstrument.bornWeight outcome (diagonalAResource p) =
      if outcome = .positive then p.cleanWeight else p.rate := by sorry
