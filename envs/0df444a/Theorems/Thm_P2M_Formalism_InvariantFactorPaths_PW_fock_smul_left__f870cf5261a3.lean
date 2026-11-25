-- Prove2me | Theorems.Thm_P2M_Formalism_InvariantFactorPaths_PW_fock_smul_left__f870cf5261a3
-- name    : P2M_Formalism_InvariantFactorPaths_PW_fock_smul_left__f870cf5261a3
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:58:19.819906+00:00
-- url     : https://prove2.me/theorems/08e3a451-5a8f-4491-a37d-d340c285ef9d
-- title:
--   P2 M Formalism Invariant Factor Paths PW fock smul left  f870cf5261a3: P2 M Formalism Invariant Factor Paths PW fock smul left  f870cf5261a3
-- statement:
--   The P2 M Formalism Invariant Factor Paths PW fock smul left  f870cf5261a3 construction uses the P2 M Formalism Invariant Factor Paths PW fock smul left  f870cf5261a3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/FischerAdjointnessHolds.lean#L41-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/FischerAdjointnessHolds.lean#L41-L42

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

theorem P2M_Formalism_InvariantFactorPaths_PW_fock_smul_left__f870cf5261a3 (c : ℚ_[p]) (F G : MvPolynomial σ ℚ_[p]) : fock p (c • F) G = c * fock p F G := by sorry

alias «Formalism».«InvariantFactorPaths».«PW».«fock_smul_left'» := P2M_Formalism_InvariantFactorPaths_PW_fock_smul_left__f870cf5261a3
