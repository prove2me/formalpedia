-- Prove2me | Theorems.Thm_P2M_Formalism_InvariantFactorPaths_PW_fock_neg_right__1b4931ed2b50
-- name    : P2M_Formalism_InvariantFactorPaths_PW_fock_neg_right__1b4931ed2b50
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:42:45.991605+00:00
-- url     : https://prove2.me/theorems/aafb38ac-8ab0-4b9d-aece-814d65e10dfc
-- title:
--   P2 M Formalism Invariant Factor Paths PW fock neg right  1b4931ed2b50: P2 M Formalism Invariant Factor Paths PW fock neg right  1b4931ed2b50
-- statement:
--   The P2 M Formalism Invariant Factor Paths PW fock neg right  1b4931ed2b50 construction uses the P2 M Formalism Invariant Factor Paths PW fock neg right  1b4931ed2b50 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/FischerAdjointnessHolds.lean#L50-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/FischerAdjointnessHolds.lean#L50-L51

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

theorem P2M_Formalism_InvariantFactorPaths_PW_fock_neg_right__1b4931ed2b50 (F G : MvPolynomial σ ℚ_[p]) : fock p F (-G) = -fock p F G := by sorry

alias «Formalism».«InvariantFactorPaths».«PW».«fock_neg_right'» := P2M_Formalism_InvariantFactorPaths_PW_fock_neg_right__1b4931ed2b50
