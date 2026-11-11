-- Prove2me | Theorems.Thm_QEC_Distillation_OneQubitMagic_projectionSquaredOverlap_conjDensity
-- name    : QEC.Distillation.OneQubitMagic.projectionSquaredOverlap_conjDensity
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T12:10:36.286663+00:00
-- url     : https://prove2.me/theorems/11023e28-720f-4535-b8f9-584fdf4320ad
-- title:
--   One Qubit Magic: projection Squared Overlap conj Density
-- statement:
--   The One Qubit Magic construction uses the projection Squared Overlap conj Density property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/OneQubitMagicState.lean#L848-L856
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/OneQubitMagicState.lean#L848-L856

import Definitions.Def_QEC_Distillation_Universality_OneQubitClifford
import Definitions.Def_QEC_Distillation_Universality_OneQubitMagicState
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit

theorem QEC.Distillation.OneQubitMagic.projectionSquaredOverlap_conjDensity
    (U : UnitaryTransport QubitSpace QubitSpace)
    (P : Operator QubitSpace) (rho : DensityOperator QubitSpace) :
    projectionSquaredOverlap (U.conjOperator P) (U.conjDensity rho) =
      projectionSquaredOverlap P rho := by sorry
