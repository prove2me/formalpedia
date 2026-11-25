-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GradedSubquot_span_monTimes_le_d973d73a9be6
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_GradedSubquot_span_monTimes_le_d973d73a9be6
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:19:40.680886+00:00
-- url     : https://prove2.me/theorems/f5f8ac1a-3187-4ffd-84bc-00545a0e7f1d
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Graded Subquot span mon Times le d973d73a9be6: P2 M Ground Theory Heights  Heights Hilbert Samuel Graded Subquot span mon Times le d973d73a9be6
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Graded Subquot span mon Times le d973d73a9be6 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Graded Subquot span mon Times le d973d73a9be6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGradedSubquot.lean#L77-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGradedSubquot.lean#L77-L79

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_GradedSubquot_span_monTimes_le_d973d73a9be6 (H : Set M) :
    Submodule.span S (monTimes S ι H) ≤ (Submodule.span (MRingOver S ι) H).restrictScalars S := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«GradedSubquot».«span_monTimes_le» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_GradedSubquot_span_monTimes_le_d973d73a9be6
