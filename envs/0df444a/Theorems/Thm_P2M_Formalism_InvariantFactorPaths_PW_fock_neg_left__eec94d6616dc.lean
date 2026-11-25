-- Prove2me | Theorems.Thm_P2M_Formalism_InvariantFactorPaths_PW_fock_neg_left__eec94d6616dc
-- name    : P2M_Formalism_InvariantFactorPaths_PW_fock_neg_left__eec94d6616dc
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:58:08.399537+00:00
-- url     : https://prove2.me/theorems/25a49f7e-8b82-4955-b150-3d723511d533
-- title:
--   P2 M Formalism Invariant Factor Paths PW fock neg left  eec94d6616dc: P2 M Formalism Invariant Factor Paths PW fock neg left  eec94d6616dc
-- statement:
--   The P2 M Formalism Invariant Factor Paths PW fock neg left  eec94d6616dc construction uses the P2 M Formalism Invariant Factor Paths PW fock neg left  eec94d6616dc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/FischerAdjointnessHolds.lean#L53-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/FischerAdjointnessHolds.lean#L53-L54

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_FischerAdjointnessHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {σ : Type}

theorem P2M_Formalism_InvariantFactorPaths_PW_fock_neg_left__eec94d6616dc (F G : MvPolynomial σ ℚ_[p]) : fock p (-F) G = -fock p F G := by sorry

alias «Formalism».«InvariantFactorPaths».«PW».«fock_neg_left'» := P2M_Formalism_InvariantFactorPaths_PW_fock_neg_left__eec94d6616dc
