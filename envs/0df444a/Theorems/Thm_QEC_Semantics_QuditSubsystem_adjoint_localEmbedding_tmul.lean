-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_adjoint_localEmbedding_tmul
-- name    : QEC.Semantics.QuditSubsystem.adjoint_localEmbedding_tmul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:20:12.477794+00:00
-- url     : https://prove2.me/theorems/80555dc6-3922-4327-bc1a-24c714ba1a6e
-- title:
--   Qudit Subsystem: adjoint local Embedding tmul
-- statement:
--   The Qudit Subsystem construction uses the adjoint local Embedding tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L299-L306
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L299-L306

import Definitions.Def_QEC_Semantics_Channels_Core
import Mathlib.Analysis.InnerProductSpace.PiL2
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Semantics.QuditSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}
set_option maxHeartbeats 800000

theorem QEC.Semantics.QuditSubsystem.adjoint_localEmbedding_tmul (S : QuditSubsystem q) (hq : ∀ i, 0 < q i)
    (h : S.selectedSystem) (k : S.complementSystem) :
    LinearMap.adjoint (S.localEmbedding hq) (h ⊗ₜ[Complex] k) =
      (inner Complex (S.complementAnchor hq) k) • h := by sorry
