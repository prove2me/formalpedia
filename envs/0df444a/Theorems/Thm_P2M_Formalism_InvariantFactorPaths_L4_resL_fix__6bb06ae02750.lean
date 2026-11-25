-- Prove2me | Theorems.Thm_P2M_Formalism_InvariantFactorPaths_L4_resL_fix__6bb06ae02750
-- name    : P2M_Formalism_InvariantFactorPaths_L4_resL_fix__6bb06ae02750
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:58:06.21608+00:00
-- url     : https://prove2.me/theorems/8834b838-03c1-4c28-a079-7ac08aa99a08
-- title:
--   P2 M Formalism Invariant Factor Paths L4 res L fix  6bb06ae02750: P2 M Formalism Invariant Factor Paths L4 res L fix  6bb06ae02750
-- statement:
--   The P2 M Formalism Invariant Factor Paths L4 res L fix  6bb06ae02750 construction uses the P2 M Formalism Invariant Factor Paths L4 res L fix  6bb06ae02750 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/HighestVectorProjection.lean#L93-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/HighestVectorProjection.lean#L93-L103

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

theorem P2M_Formalism_InvariantFactorPaths_L4_resL_fix__6bb06ae02750 {σ : Type} (v : σ) (x : MvPolynomial σ ℚ_[p]) (hx : x ∈ FreeOf p v) : resL p v 0 x = x := by sorry

alias «Formalism».«InvariantFactorPaths».«L4».«resL_fix'» := P2M_Formalism_InvariantFactorPaths_L4_resL_fix__6bb06ae02750
