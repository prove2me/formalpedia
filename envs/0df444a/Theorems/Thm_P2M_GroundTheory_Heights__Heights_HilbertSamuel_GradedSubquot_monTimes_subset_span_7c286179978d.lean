-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GradedSubquot_monTimes_subset_span_7c286179978d
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_GradedSubquot_monTimes_subset_span_7c286179978d
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:28:24.455961+00:00
-- url     : https://prove2.me/theorems/bc93b0be-9fec-454b-a614-64085bf58eb7
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Graded Subquot mon Times subset span 7c286179978d: P2 M Ground Theory Heights  Heights Hilbert Samuel Graded Subquot mon Times subset span 7c28617997
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Graded Subquot mon Times subset span 7c286179978d construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Graded Subquot mon Times subset span 7c286179978d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGradedSubquot.lean#L73-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGradedSubquot.lean#L73-L75

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_GradedSubquot_monTimes_subset_span_7c286179978d (H : Set M) : monTimes S ι H ⊆ Submodule.span (MRingOver S ι) H := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«GradedSubquot».«monTimes_subset_span» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_GradedSubquot_monTimes_subset_span_7c286179978d
