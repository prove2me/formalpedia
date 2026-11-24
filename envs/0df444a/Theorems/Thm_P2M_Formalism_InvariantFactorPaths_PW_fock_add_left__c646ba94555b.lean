-- Prove2me | Theorems.Thm_P2M_Formalism_InvariantFactorPaths_PW_fock_add_left__c646ba94555b
-- name    : P2M_Formalism_InvariantFactorPaths_PW_fock_add_left__c646ba94555b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:20:01.628185+00:00
-- url     : https://prove2.me/theorems/94a9cb95-9d0a-41ed-92ce-6147ce35474a
-- title:
--   P2 M Formalism Invariant Factor Paths PW fock add left  c646ba94555b: P2 M Formalism Invariant Factor Paths PW fock add left  c646ba94555b
-- statement:
--   The P2 M Formalism Invariant Factor Paths PW fock add left  c646ba94555b construction uses the P2 M Formalism Invariant Factor Paths PW fock add left  c646ba94555b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/FischerAdjointnessHolds.lean#L38-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/FischerAdjointnessHolds.lean#L38-L39

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

theorem P2M_Formalism_InvariantFactorPaths_PW_fock_add_left__c646ba94555b (F F' G : MvPolynomial σ ℚ_[p]) : fock p (F + F') G = fock p F G + fock p F' G := by sorry

alias «Formalism».«InvariantFactorPaths».«PW».«fock_add_left'» := P2M_Formalism_InvariantFactorPaths_PW_fock_add_left__c646ba94555b
