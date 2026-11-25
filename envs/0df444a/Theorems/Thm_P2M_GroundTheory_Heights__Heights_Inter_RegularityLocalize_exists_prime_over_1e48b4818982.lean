-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RegularityLocalize_exists_prime_over_1e48b4818982
-- name    : P2M_GroundTheory_Heights__Heights_Inter_RegularityLocalize_exists_prime_over_1e48b4818982
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:44:34.44615+00:00
-- url     : https://prove2.me/theorems/13c70f43-aeae-4207-be23-b4fc9ff8a6f9
-- title:
--   P2 M Ground Theory Heights  Heights Inter Regularity Localize exists prime over 1e48b4818982: P2 M Ground Theory Heights  Heights Inter Regularity Localize exists prime over 1e48b4818982
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Regularity Localize exists prime over 1e48b4818982 construction uses the P2 M Ground Theory Heights  Heights Inter Regularity Localize exists prime over 1e48b4818982 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ImportsBisRest.lean#L14-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ImportsBisRest.lean#L14-L22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsMoreTer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsMoreAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IntCastMemRegMaxAt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsBisAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsBisRest
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Inter_RegularityLocalize_exists_prime_over_1e48b4818982 {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P W : Ideal (MRing ι)} (hP : IsArithVar P 1) (hW : IsClosedPt W) :
    ∃ p : ℤ, Prime p ∧ ∀ k : ℤ, C k ∈ W ↔ p ∣ k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«RegularityLocalize».«exists_prime_over» := P2M_GroundTheory_Heights__Heights_Inter_RegularityLocalize_exists_prime_over_1e48b4818982
