-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GradedSubquot_span_le_span_monTimes_4833d8b0dfcc
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_GradedSubquot_span_le_span_monTimes_4833d8b0dfcc
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:19:20.229701+00:00
-- url     : https://prove2.me/theorems/7345edc6-9c43-55e8-a792-486ab33e0fd2
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Graded Subquot span le span mon Times 4833d8b0dfcc: P2 M Ground Theory Heights  Heights Hilbert Samuel Graded Subquot span le span mon Times 4833d8b0
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Graded Subquot span le span mon Times 4833d8b0dfcc construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Graded Subquot span le span mon Times 4833d8b0dfcc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGradedSubquot.lean#L93-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGradedSubquot.lean#L93-L114

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_GradedSubquot_span_le_span_monTimes_4833d8b0dfcc (H : Set M) :
    (Submodule.span (MRingOver S ι) H).restrictScalars S ≤ Submodule.span S (monTimes S ι H) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«GradedSubquot».«span_le_span_monTimes» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_GradedSubquot_span_le_span_monTimes_4833d8b0dfcc
