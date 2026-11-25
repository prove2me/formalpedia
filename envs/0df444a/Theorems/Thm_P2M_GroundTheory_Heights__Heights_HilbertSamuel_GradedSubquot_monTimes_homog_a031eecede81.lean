-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GradedSubquot_monTimes_homog_a031eecede81
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_GradedSubquot_monTimes_homog_a031eecede81
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:19:26.579653+00:00
-- url     : https://prove2.me/theorems/6aae6122-2a81-5d3b-9e5c-2fee59f2b306
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Graded Subquot mon Times homog a031eecede81: P2 M Ground Theory Heights  Heights Hilbert Samuel Graded Subquot mon Times homog a031eecede81
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Graded Subquot mon Times homog a031eecede81 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Graded Subquot mon Times homog a031eecede81 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGradedSubquot.lean#L116-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGradedSubquot.lean#L116-L120

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsGradedSubquot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGradedSubquot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.GradedSubquot
set_option linter.unusedSectionVars false
variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_GradedSubquot_monTimes_homog_a031eecede81 {𝓜 : (K → ℤ) → Submodule S M} (hM : KH.IsMGraded S ι 𝓜) {H : Set M}
    (hH : ∀ x ∈ H, ∃ c, x ∈ 𝓜 c) {y : M} (hy : y ∈ monTimes S ι H) : ∃ c, y ∈ 𝓜 c := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«GradedSubquot».«monTimes_homog» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_GradedSubquot_monTimes_homog_a031eecede81
