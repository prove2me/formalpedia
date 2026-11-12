-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_depthTwoChildSelectedPortTransportedDensity_eq_selectedPortDensity
-- name    : QEC.Distillation.Triorthogonal.BH12Concatenation.depthTwoChildSelectedPortTransportedDensity_eq_selectedPortDensity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T22:30:44.384732+00:00
-- url     : https://prove2.me/theorems/9c61b747-dbc0-472e-b0a6-fab6495377fa
-- title:
--   BH12 Concatenation: depth Two Child Selected Port Transported Density eq selected Port Density
-- statement:
--   The BH12 Concatenation construction uses the depth Two Child Selected Port Transported Density eq selected Port Density property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L1397-L1405
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L1397-L1405

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_Core_Overhead
import Definitions.Def_QEC_Distillation_Triorthogonal_Concatenation
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12Concatenation
open Semantics
open BH12EvenFamily
open BH12NoisyInjection
open BH12Protocol
open Filter Topology

theorem QEC.Distillation.Triorthogonal.BH12Concatenation.depthTwoChildSelectedPortTransportedDensity_eq_selectedPortDensity
    (q : Nat) (p : ErrorParameter) (hsuccess : 0 < rawSuccessMass q p)
    (firstPort secondPort : OddRow q) :
    depthTwoChildSelectedPortTransportedDensity q p firstPort secondPort =
      bh12SelectedPortTransportedDensity q
        (bh12DecodedMarginalErrorParameter q p hsuccess firstPort) secondPort := by sorry
