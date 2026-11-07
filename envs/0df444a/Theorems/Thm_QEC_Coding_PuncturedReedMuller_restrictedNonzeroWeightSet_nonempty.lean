-- Prove2me | Theorems.Thm_QEC_Coding_PuncturedReedMuller_restrictedNonzeroWeightSet_nonempty
-- name    : QEC.Coding.PuncturedReedMuller.restrictedNonzeroWeightSet_nonempty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:03:18.016307+00:00
-- url     : https://prove2.me/theorems/06c7a995-fdf4-482e-8622-696e6756430b
-- title:
--   Punctured Reed Muller: restricted Nonzero Weight Set nonempty
-- statement:
--   Actual RM evaluations provide a nonempty spectrum even when the coordinate
--   restriction itself has no retained support.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedMuller/Punctured.lean#L793-L798
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedMuller/Punctured.lean#L793-L798

import Definitions.Def_QEC_Coding_ReedMuller_Base
import Definitions.Def_QEC_Coding_ReedMuller_Punctured
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PuncturedReedMuller
open ReedMuller

theorem QEC.Coding.PuncturedReedMuller.restrictedNonzeroWeightSet_nonempty (r m w : Nat) :
    (restrictedNonzeroWeightSet r m w).Nonempty := by sorry
