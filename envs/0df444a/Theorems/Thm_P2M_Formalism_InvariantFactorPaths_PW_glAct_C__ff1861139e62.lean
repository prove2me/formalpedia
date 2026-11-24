-- Prove2me | Theorems.Thm_P2M_Formalism_InvariantFactorPaths_PW_glAct_C__ff1861139e62
-- name    : P2M_Formalism_InvariantFactorPaths_PW_glAct_C__ff1861139e62
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:19:36.261588+00:00
-- url     : https://prove2.me/theorems/eefa33d2-2e94-4c13-b4d6-c915f34e15b4
-- title:
--   P2 M Formalism Invariant Factor Paths PW gl Act C  ff1861139e62: P2 M Formalism Invariant Factor Paths PW gl Act C  ff1861139e62
-- statement:
--   The P2 M Formalism Invariant Factor Paths PW gl Act C  ff1861139e62 construction uses the P2 M Formalism Invariant Factor Paths PW gl Act C  ff1861139e62 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/FischerAdjointnessHolds.lean#L226-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/FischerAdjointnessHolds.lean#L226-L229

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
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem P2M_Formalism_InvariantFactorPaths_PW_glAct_C__ff1861139e62 (LL : Letters N) (j : ℕ) (c d : Fin r) (a : ℚ_[p]) : glAct p LL j c d (C a) = 0 := by sorry

alias «Formalism».«InvariantFactorPaths».«PW».«glAct_C'» := P2M_Formalism_InvariantFactorPaths_PW_glAct_C__ff1861139e62
