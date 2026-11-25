-- Prove2me | Theorems.Thm_P2M_Formalism_InvariantFactorPaths_L4_lowIm_keep__abc410c6108a
-- name    : P2M_Formalism_InvariantFactorPaths_L4_lowIm_keep__abc410c6108a
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:57:45.718016+00:00
-- url     : https://prove2.me/theorems/c08d5748-3905-4ce7-9144-96fa957b1ec8
-- title:
--   P2 M Formalism Invariant Factor Paths L4 low Im keep  abc410c6108a: P2 M Formalism Invariant Factor Paths L4 low Im keep  abc410c6108a
-- statement:
--   The P2 M Formalism Invariant Factor Paths L4 low Im keep  abc410c6108a construction uses the P2 M Formalism Invariant Factor Paths L4 low Im keep  abc410c6108a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/HighestVectorProjection.lean#L45-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/HighestVectorProjection.lean#L45-L57

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

theorem P2M_Formalism_InvariantFactorPaths_L4_lowIm_keep__abc410c6108a (LL : Letters N) (j : ℕ) (ρ : Fin r)
    (A : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hA : ∀ c ∈ univ.erase ρ, ∀ d ∈ univ.erase ρ, ∀ x, A (glAct p LL j c d x) = glAct p LL j c d (A x)) :
    ∀ x ∈ lowIm' p LL j ρ, A x ∈ lowIm' p LL j ρ := by sorry

alias «Formalism».«InvariantFactorPaths».«L4».«lowIm_keep'» := P2M_Formalism_InvariantFactorPaths_L4_lowIm_keep__abc410c6108a
