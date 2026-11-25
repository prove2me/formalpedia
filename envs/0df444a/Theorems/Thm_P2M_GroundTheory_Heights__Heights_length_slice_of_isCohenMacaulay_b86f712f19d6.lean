-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_length_slice_of_isCohenMacaulay_b86f712f19d6
-- name    : P2M_GroundTheory_Heights__Heights_length_slice_of_isCohenMacaulay_b86f712f19d6
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:48:24.8105+00:00
-- url     : https://prove2.me/theorems/1a617fc4-d65c-4419-82ea-d4f29d0ba9ce
-- title:
--   P2 M Ground Theory Heights  Heights length slice of is Cohen Macaulay b86f712f19d6: P2 M Ground Theory Heights  Heights length slice of is Cohen Macaulay b86f712f19d6
-- statement:
--   The P2 M Ground Theory Heights  Heights length slice of is Cohen Macaulay b86f712f19d6 construction uses the P2 M Ground Theory Heights  Heights length slice of is Cohen Macaulay b86f712f19d6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLengthTransverseSlice.lean#L13-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLengthTransverseSlice.lean#L13-L101

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLengthTransverseSlice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLocalDimDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMLengthParameters
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalizeQuotientStages
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLengthTransverseSlice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Matrix ComplexSets IsLocalRing

theorem P2M_GroundTheory_Heights__Heights_length_slice_of_isCohenMacaulay_b86f712f19d6 (hCM : CMLengthParameters.Statement.{0})
    (hLS : LocalizeQuotientStages.Statement.{0}) {R : Type} [CommRing R] (m W I : Ideal R) [m.IsPrime] [W.IsPrime]
    [IsCohenMacaulayLocalRing (Localization.AtPrime m ⧸ I.map (algebraMap R (Localization.AtPrime m)))]
    (hW : W ∈ I.minimalPrimes) (hWm : W ≤ m) (huniq : ∀ W' ∈ I.minimalPrimes, W' ≤ m → W' = W)
    (d : ℕ) (lin : Fin d → R) (hlin : ∀ i, lin i ∈ m)
    (hdim : ringKrullDim (Localization.AtPrime m ⧸ W.map (algebraMap R (Localization.AtPrime m))) = (d : ℕ))
    (hT : ∀ g ∈ m, ∃ s ∉ m, s * g ∈ W ⊔ Ideal.span (Set.range lin)) :
    Module.length (Localization.AtPrime W) (Localization.AtPrime W ⧸ I.map (algebraMap R (Localization.AtPrime W))) =
      Module.length (Localization.AtPrime m)
        (Localization.AtPrime m ⧸ (I ⊔ Ideal.span (Set.range lin)).map (algebraMap R (Localization.AtPrime m))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«length_slice_of_isCohenMacaulay» := P2M_GroundTheory_Heights__Heights_length_slice_of_isCohenMacaulay_b86f712f19d6
