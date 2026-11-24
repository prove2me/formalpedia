-- Prove2me | Theorems.Thm_P2M_Formalism_InvariantFactorPaths_PW_fock_symm__e96ddd2ea090
-- name    : P2M_Formalism_InvariantFactorPaths_PW_fock_symm__e96ddd2ea090
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:19:21.111967+00:00
-- url     : https://prove2.me/theorems/1b7f7d8f-9cab-41ee-822f-fbc09278e1b1
-- title:
--   P2 M Formalism Invariant Factor Paths PW fock symm  e96ddd2ea090: P2 M Formalism Invariant Factor Paths PW fock symm  e96ddd2ea090
-- statement:
--   The P2 M Formalism Invariant Factor Paths PW fock symm  e96ddd2ea090 construction uses the P2 M Formalism Invariant Factor Paths PW fock symm  e96ddd2ea090 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/FischerAdjointnessHolds.lean#L18-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/FischerAdjointnessHolds.lean#L18-L22

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

theorem P2M_Formalism_InvariantFactorPaths_PW_fock_symm__e96ddd2ea090 (F G : MvPolynomial σ ℚ_[p]) : fock p F G = fock p G F := by sorry

alias «Formalism».«InvariantFactorPaths».«PW».«fock_symm'» := P2M_Formalism_InvariantFactorPaths_PW_fock_symm__e96ddd2ea090
