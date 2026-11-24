-- Prove2me | Theorems.Thm_P2M_Formalism_InvariantFactorPaths_PW_fock_add_right__407452ae58c2
-- name    : P2M_Formalism_InvariantFactorPaths_PW_fock_add_right__407452ae58c2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:19:20.81481+00:00
-- url     : https://prove2.me/theorems/d9332c6c-b1b7-4fb4-a3ab-afa863690728
-- title:
--   P2 M Formalism Invariant Factor Paths PW fock add right  407452ae58c2: P2 M Formalism Invariant Factor Paths PW fock add right  407452ae58c2
-- statement:
--   The P2 M Formalism Invariant Factor Paths PW fock add right  407452ae58c2 construction uses the P2 M Formalism Invariant Factor Paths PW fock add right  407452ae58c2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/FischerAdjointnessHolds.lean#L24-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/FischerAdjointnessHolds.lean#L24-L29

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

theorem P2M_Formalism_InvariantFactorPaths_PW_fock_add_right__407452ae58c2 (F G G' : MvPolynomial σ ℚ_[p]) : fock p F (G + G') = fock p F G + fock p F G' := by sorry

alias «Formalism».«InvariantFactorPaths».«PW».«fock_add_right'» := P2M_Formalism_InvariantFactorPaths_PW_fock_add_right__407452ae58c2
