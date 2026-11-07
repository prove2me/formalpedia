-- Prove2me | Theorems.Thm_QEC_Coding_CSSGibbs_sector_zero_eq_code
-- name    : QEC.Coding.CSSGibbs.sector_zero_eq_code
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:05:50.832533+00:00
-- url     : https://prove2.me/theorems/db1d83cd-8b1c-4fbd-80b6-28cb97b2c49e
-- title:
--   CSSGibbs: sector zero eq code
-- statement:
--   The zero sector is the actual semantic CSS code carrier.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Projectors.lean#L342-L360
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Projectors.lean#L342-L360

import Definitions.Def_QEC_Coding_CSS_Syndrome
import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Coding_Stabilizer_BasisAction
import Definitions.Def_QEC_Semantics_Core_OperatorTraceNorm
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Projectors
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.CSSGibbs
open Classical PauliSymplectic StabilizerCode Semantics
open scoped BigOperators
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable {κP κQ : Type} [Fintype κP] [Fintype κQ] [DecidableEq κP] [DecidableEq κQ]
variable (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
  (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
  (horth : ∀ p q, wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)

theorem QEC.Coding.CSSGibbs.sector_zero_eq_code : sector P Q horth 0 =
    (binaryCSSQuantumCodeOfDualLe (parityCheckRowCode Q) (parityCheckRowCode P)
      ((parityCheckRows_orthogonal_iff_rowCode_le_dual P Q).mp horth)).carrier := by sorry
