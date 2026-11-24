-- Prove2me | Theorems.Thm_P2M_Formalism_InvariantFactorPaths_PW_fock_zero_left__85aaa0c1d77b
-- name    : P2M_Formalism_InvariantFactorPaths_PW_fock_zero_left__85aaa0c1d77b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:19:31.788811+00:00
-- url     : https://prove2.me/theorems/0795d2f9-c362-4fb8-afcb-a449ae1c190a
-- title:
--   P2 M Formalism Invariant Factor Paths PW fock zero left  85aaa0c1d77b: P2 M Formalism Invariant Factor Paths PW fock zero left  85aaa0c1d77b
-- statement:
--   The P2 M Formalism Invariant Factor Paths PW fock zero left  85aaa0c1d77b construction uses the P2 M Formalism Invariant Factor Paths PW fock zero left  85aaa0c1d77b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/FischerAdjointnessHolds.lean#L44-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/FischerAdjointnessHolds.lean#L44-L45

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

theorem P2M_Formalism_InvariantFactorPaths_PW_fock_zero_left__85aaa0c1d77b (G : MvPolynomial σ ℚ_[p]) : fock p 0 G = 0 := by sorry

alias «Formalism».«InvariantFactorPaths».«PW».«fock_zero_left'» := P2M_Formalism_InvariantFactorPaths_PW_fock_zero_left__85aaa0c1d77b
