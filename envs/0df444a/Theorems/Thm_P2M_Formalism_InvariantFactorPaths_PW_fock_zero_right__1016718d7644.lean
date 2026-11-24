-- Prove2me | Theorems.Thm_P2M_Formalism_InvariantFactorPaths_PW_fock_zero_right__1016718d7644
-- name    : P2M_Formalism_InvariantFactorPaths_PW_fock_zero_right__1016718d7644
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:19:28.040051+00:00
-- url     : https://prove2.me/theorems/88bcdbce-693a-4588-bfd0-595aa8ddf864
-- title:
--   P2 M Formalism Invariant Factor Paths PW fock zero right  1016718d7644: P2 M Formalism Invariant Factor Paths PW fock zero right  1016718d7644
-- statement:
--   The P2 M Formalism Invariant Factor Paths PW fock zero right  1016718d7644 construction uses the P2 M Formalism Invariant Factor Paths PW fock zero right  1016718d7644 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/FischerAdjointnessHolds.lean#L47-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/FischerAdjointnessHolds.lean#L47-L48

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

theorem P2M_Formalism_InvariantFactorPaths_PW_fock_zero_right__1016718d7644 (F : MvPolynomial σ ℚ_[p]) : fock p F 0 = 0 := by sorry

alias «Formalism».«InvariantFactorPaths».«PW».«fock_zero_right'» := P2M_Formalism_InvariantFactorPaths_PW_fock_zero_right__1016718d7644
