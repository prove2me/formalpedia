-- Prove2me | Theorems.Thm_P2M_Formalism_InvariantFactorPaths_PW_fock_eq_sum__18511f081048
-- name    : P2M_Formalism_InvariantFactorPaths_PW_fock_eq_sum__18511f081048
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:42:37.515207+00:00
-- url     : https://prove2.me/theorems/ffc0c653-7925-49b6-b1e5-bd5d56aaf449
-- title:
--   P2 M Formalism Invariant Factor Paths PW fock eq sum  18511f081048: P2 M Formalism Invariant Factor Paths PW fock eq sum  18511f081048
-- statement:
--   The P2 M Formalism Invariant Factor Paths PW fock eq sum  18511f081048 construction uses the P2 M Formalism Invariant Factor Paths PW fock eq sum  18511f081048 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/FischerAdjointnessHolds.lean#L11-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/FischerAdjointnessHolds.lean#L11-L16

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

theorem P2M_Formalism_InvariantFactorPaths_PW_fock_eq_sum__18511f081048 (F G : MvPolynomial σ ℚ_[p]) (s : Finset (σ →₀ ℕ)) (hs : F.support ⊆ s) :
    fock p F G = ∑ m ∈ s, F.coeff m * G.coeff m * (m.prod fun _ k => (k.factorial : ℚ_[p])) := by sorry

alias «Formalism».«InvariantFactorPaths».«PW».«fock_eq_sum'» := P2M_Formalism_InvariantFactorPaths_PW_fock_eq_sum__18511f081048
