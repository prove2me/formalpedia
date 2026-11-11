-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDifferentialMasks_mask_commutes_iff_matrix
-- name    : QEC.Coding.BDL26RXDifferentialMasks.mask_commutes_iff_matrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:56:40.410768+00:00
-- url     : https://prove2.me/theorems/e30612b1-8fa6-4bde-8e81-9a72a5027522
-- title:
--   BDL26 RXDifferential Masks: mask commutes iff matrix
-- statement:
--   An all-input mask identity is exactly a condition on every NONZERO
--   matrix coefficient. Zero coefficients impose no condition on either mask.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXDifferentialMasks.lean#L53-L96
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXDifferentialMasks.lean#L53-L96

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXQConcreteCoherence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXDifferentialMasks
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXDifferentialMasks
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXQConcreteCoherence
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXDifferentialMasks.mask_commutes_iff_matrix
    {C E : Type} [Fintype C] [DecidableEq C] [Fintype E] [DecidableEq E]
    (T : Word BDL26Field C →ₗ[BDL26Field] Word BDL26Field E)
    (A : Finset C) (B : Finset E) :
    (∀ w, maskWord B (T w) = T (maskWord A w)) ↔
      ∀ q p, T (canonicalBasisWord q) p ≠ 0 → (p ∈ B ↔ q ∈ A) := by sorry
