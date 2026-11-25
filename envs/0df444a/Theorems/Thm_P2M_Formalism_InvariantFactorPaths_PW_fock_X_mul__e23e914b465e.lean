-- Prove2me | Theorems.Thm_P2M_Formalism_InvariantFactorPaths_PW_fock_X_mul__e23e914b465e
-- name    : P2M_Formalism_InvariantFactorPaths_PW_fock_X_mul__e23e914b465e
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:58:00.912806+00:00
-- url     : https://prove2.me/theorems/b7387e48-bc87-4b0e-987a-54139efc61a7
-- title:
--   P2 M Formalism Invariant Factor Paths PW fock X mul  e23e914b465e: P2 M Formalism Invariant Factor Paths PW fock X mul  e23e914b465e
-- statement:
--   The P2 M Formalism Invariant Factor Paths PW fock X mul  e23e914b465e construction uses the P2 M Formalism Invariant Factor Paths PW fock X mul  e23e914b465e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/FischerAdjointnessHolds.lean#L99-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/FischerAdjointnessHolds.lean#L99-L107

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

theorem P2M_Formalism_InvariantFactorPaths_PW_fock_X_mul__e23e914b465e (i : σ) (g h : MvPolynomial σ ℚ_[p]) :
    fock p (X i * g) h = fock p g (pderiv i h) := by sorry

alias «Formalism».«InvariantFactorPaths».«PW».«fock_X_mul'» := P2M_Formalism_InvariantFactorPaths_PW_fock_X_mul__e23e914b465e
