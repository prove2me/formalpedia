-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_isCohenMacaulayLocalRing_quotient_iff_of_isRegularLocalRing_3eacb56911f2
-- name    : P2M_GroundTheory_Heights__Heights_isCohenMacaulayLocalRing_quotient_iff_of_isRegularLocalRing_3eacb56911f2
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:47:46.633699+00:00
-- url     : https://prove2.me/theorems/94c67e4f-d235-4e95-a72a-ae031abd4837
-- title:
--   P2 M Ground Theory Heights  Heights is Cohen Macaulay Local Ring quotient iff of is Regular Local Ring 3eacb56911f2: P2 M Ground Theory Heights  Heights is Cohen Macaulay Local Ring quotient iff of is
-- statement:
--   The P2 M Ground Theory Heights  Heights is Cohen Macaulay Local Ring quotient iff of is Regular Local Ring 3eacb56911f2 construction uses the P2 M Ground Theory Heights  Heights is Cohen Macaulay Local Ring quotient iff of is Regular Local Ring 3eacb56911f2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCMProjDimCriterion.lean#L43-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCMProjDimCriterion.lean#L43-L103

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularUFDSerre
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularSmooth
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMProjDimCriterion
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAuslanderBuchsbaumDepthLower
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAuslanderBuchsbaumProjDimUpper
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegularSequenceLengthLeDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMHeightAddDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCMProjDimCriterion
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
open IsLocalRing CategoryTheory RingTheory.Sequence

theorem P2M_GroundTheory_Heights__Heights_isCohenMacaulayLocalRing_quotient_iff_of_isRegularLocalRing_3eacb56911f2
    (hlow : AuslanderBuchsbaumDepthLower.Statement.{0}) (hup : AuslanderBuchsbaumProjDimUpper.Statement.{0})
    (hlen : RegularSequenceLengthLeDim.Statement.{0}) (hcm : CMHeightAddDim.Statement.{0})
    {S : Type} [CommRing S] [IsRegularLocalRing S] (J : Ideal S) (hJm : J ≤ maximalIdeal S) :
    IsCohenMacaulayLocalRing (S ⧸ J) ↔
      ∃ ℓ : ℕ, HasProjectiveDimensionLE (ModuleCat.of S (S ⧸ J)) ℓ ∧ (ℓ : ℕ∞) ≤ J.height := by sorry

alias «GroundTheory».«Heights₂».«Heights».«isCohenMacaulayLocalRing_quotient_iff_of_isRegularLocalRing» := P2M_GroundTheory_Heights__Heights_isCohenMacaulayLocalRing_quotient_iff_of_isRegularLocalRing_3eacb56911f2
