-- Prove2me | Theorems.Thm_P2M_Formalism_InvariantFactorPaths_PW_fock_sum_left__a0ab5af836e3
-- name    : P2M_Formalism_InvariantFactorPaths_PW_fock_sum_left__a0ab5af836e3
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:59:05.061121+00:00
-- url     : https://prove2.me/theorems/b45cdd53-9afb-42ca-af43-136d9fd6452c
-- title:
--   P2 M Formalism Invariant Factor Paths PW fock sum left  a0ab5af836e3: P2 M Formalism Invariant Factor Paths PW fock sum left  a0ab5af836e3
-- statement:
--   The P2 M Formalism Invariant Factor Paths PW fock sum left  a0ab5af836e3 construction uses the P2 M Formalism Invariant Factor Paths PW fock sum left  a0ab5af836e3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/FischerAdjointnessHolds.lean#L56-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/FischerAdjointnessHolds.lean#L56-L61

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

theorem P2M_Formalism_InvariantFactorPaths_PW_fock_sum_left__a0ab5af836e3 {ι : Type} (t : Finset ι) (F : ι → MvPolynomial σ ℚ_[p]) (G : MvPolynomial σ ℚ_[p]) :
    fock p (∑ i ∈ t, F i) G = ∑ i ∈ t, fock p (F i) G := by sorry

alias «Formalism».«InvariantFactorPaths».«PW».«fock_sum_left'» := P2M_Formalism_InvariantFactorPaths_PW_fock_sum_left__a0ab5af836e3
