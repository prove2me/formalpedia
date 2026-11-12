-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_depthTwoFreshParentPortDensity_eq_selectedPortDensity
-- name    : QEC.Distillation.Triorthogonal.BH12Concatenation.depthTwoFreshParentPortDensity_eq_selectedPortDensity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T22:30:39.948318+00:00
-- url     : https://prove2.me/theorems/f30789b9-82d4-4b12-bb63-f1e1e071b19e
-- title:
--   BH12 Concatenation: depth Two Fresh Parent Port Density eq selected Port Density
-- statement:
--   The BH12 Concatenation construction uses the depth Two Fresh Parent Port Density eq selected Port Density property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L1349-L1353
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L1349-L1353

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

theorem QEC.Distillation.Triorthogonal.BH12Concatenation.depthTwoFreshParentPortDensity_eq_selectedPortDensity (q : Nat)
    (p : ErrorParameter) (parent : Fin (bh12InputCount q)) (port : OddRow q) :
    depthTwoFreshParentPortDensity q p parent port =
      bh12SelectedPortTransportedDensity q p port := by sorry
