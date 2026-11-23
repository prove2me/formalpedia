-- Prove2me | Theorems.Thm_P2M_Formalism_InvariantFactorPaths_L4_fock_right_zero__5b3a67430530
-- name    : P2M_Formalism_InvariantFactorPaths_L4_fock_right_zero__5b3a67430530
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:05:37.295899+00:00
-- url     : https://prove2.me/theorems/ff61f8da-4e82-483b-9526-ad20bcfa6b9b
-- title:
--   P2 M Formalism Invariant Factor Paths L4 fock right zero  5b3a67430530: P2 M Formalism Invariant Factor Paths L4 fock right zero  5b3a67430530
-- statement:
--   The P2 M Formalism Invariant Factor Paths L4 fock right zero  5b3a67430530 construction uses the P2 M Formalism Invariant Factor Paths L4 fock right zero  5b3a67430530 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/HighestVectorProjection.lean#L113-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/HighestVectorProjection.lean#L113-L115

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_HighestVectorProjection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem P2M_Formalism_InvariantFactorPaths_L4_fock_right_zero__5b3a67430530 {σ : Type} (g : MvPolynomial σ ℚ_[p]) : fock p g 0 = 0 := by sorry

alias «Formalism».«InvariantFactorPaths».«L4».«fock_right_zero'» := P2M_Formalism_InvariantFactorPaths_L4_fock_right_zero__5b3a67430530
