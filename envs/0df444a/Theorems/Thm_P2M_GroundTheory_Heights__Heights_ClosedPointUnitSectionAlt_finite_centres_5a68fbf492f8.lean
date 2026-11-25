-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_finite_centres_5a68fbf492f8
-- name    : P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_finite_centres_5a68fbf492f8
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:18:36.821381+00:00
-- url     : https://prove2.me/theorems/af265002-2451-48a2-b0fa-a0c6bfe14a94
-- title:
--   P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt finite centres 5a68fbf492f8: P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt finite centres 5a68fbf492f8
-- statement:
--   The P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt finite centres 5a68fbf492f8 construction uses the P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt finite centres 5a68fbf492f8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PClosedPointUnitSection.lean#L369-L395
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PClosedPointUnitSection.lean#L369-L395

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsClosedPointUnitSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCurveCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PClosedPointUnitSection
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
open ReciprocityTheory.ChartRestriction.G.Geo NumberField IsDedekindDomain
noncomputable section
open GroundTheory.Heights₂.Heights.ClosedPointUnitSectionAlt
variable {T : Type} [Fintype T] {K' : Type} [Field K'] (y : (Σ _ : Unit, T) → K')
variable [NumberField K']
omit [Fintype T] [NumberField K']

theorem P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_finite_centres_5a68fbf492f8 [NumberField K'] (m : Ideal (curveRing y)) (hm : m.IsMaximal) :
    {P : HeightOneSpectrum (𝓞 K') |
      ∃ q : ℕ, q.Prime ∧ (q : curveRing y) ∈ m ∧ (q : 𝓞 K') ∈ P.asIdeal}.Finite := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ClosedPointUnitSectionAlt».«finite_centres» := P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_finite_centres_5a68fbf492f8
