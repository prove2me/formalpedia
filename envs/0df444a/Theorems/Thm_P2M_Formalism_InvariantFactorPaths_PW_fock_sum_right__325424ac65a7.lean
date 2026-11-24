-- Prove2me | Theorems.Thm_P2M_Formalism_InvariantFactorPaths_PW_fock_sum_right__325424ac65a7
-- name    : P2M_Formalism_InvariantFactorPaths_PW_fock_sum_right__325424ac65a7
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:42:39.064821+00:00
-- url     : https://prove2.me/theorems/86774cfe-b690-4122-8ee8-7cd9545fa981
-- title:
--   P2 M Formalism Invariant Factor Paths PW fock sum right  325424ac65a7: P2 M Formalism Invariant Factor Paths PW fock sum right  325424ac65a7
-- statement:
--   The P2 M Formalism Invariant Factor Paths PW fock sum right  325424ac65a7 construction uses the P2 M Formalism Invariant Factor Paths PW fock sum right  325424ac65a7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/FischerAdjointnessHolds.lean#L63-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/FischerAdjointnessHolds.lean#L63-L68

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

theorem P2M_Formalism_InvariantFactorPaths_PW_fock_sum_right__325424ac65a7 {ι : Type} (t : Finset ι) (F : MvPolynomial σ ℚ_[p]) (G : ι → MvPolynomial σ ℚ_[p]) :
    fock p F (∑ i ∈ t, G i) = ∑ i ∈ t, fock p F (G i) := by sorry

alias «Formalism».«InvariantFactorPaths».«PW».«fock_sum_right'» := P2M_Formalism_InvariantFactorPaths_PW_fock_sum_right__325424ac65a7
