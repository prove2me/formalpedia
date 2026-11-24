-- Prove2me | Theorems.Thm_P2M_Formalism_InvariantFactorPaths_PW_fock_smul_right__50546d9c35a2
-- name    : P2M_Formalism_InvariantFactorPaths_PW_fock_smul_right__50546d9c35a2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:19:38.387193+00:00
-- url     : https://prove2.me/theorems/c895c623-fbdc-4bcf-b83b-4e4a5ef6ea76
-- title:
--   P2 M Formalism Invariant Factor Paths PW fock smul right  50546d9c35a2: P2 M Formalism Invariant Factor Paths PW fock smul right  50546d9c35a2
-- statement:
--   The P2 M Formalism Invariant Factor Paths PW fock smul right  50546d9c35a2 construction uses the P2 M Formalism Invariant Factor Paths PW fock smul right  50546d9c35a2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/FischerAdjointnessHolds.lean#L31-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/FischerAdjointnessHolds.lean#L31-L36

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

theorem P2M_Formalism_InvariantFactorPaths_PW_fock_smul_right__50546d9c35a2 (c : ℚ_[p]) (F G : MvPolynomial σ ℚ_[p]) : fock p F (c • G) = c * fock p F G := by sorry

alias «Formalism».«InvariantFactorPaths».«PW».«fock_smul_right'» := P2M_Formalism_InvariantFactorPaths_PW_fock_smul_right__50546d9c35a2
