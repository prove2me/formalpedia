-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ResBridge_interior_D_8a07618018ce
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_ResBridge_interior_D_8a07618018ce
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T16:28:33.076179+00:00
-- url     : https://prove2.me/theorems/b27bfc81-0201-4572-8801-d77cb50a9b62
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Res Bridge interior D 8a07618018ce: P2 M Ground Theory Heights  Heights Hilbert Samuel Res Bridge interior D 8a07618018ce
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Res Bridge interior D 8a07618018ce construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Res Bridge interior D 8a07618018ce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/ComponentResBadNullFlat.lean#L45-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/ComponentResBadNullFlat.lean#L45-L78

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ComponentResBadNullLift
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_AnalyticSubsetChartLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeK
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ComponentResBadNullFlat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel GroundTheory.Heights₂.Heights.HilbertSamuel.ResBridge
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Topology Filter Set
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {W : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ} (R : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Res ι W e)

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_ResBridge_interior_D_8a07618018ce : interior {x | R.pt x ∈ ReciprocityTheory.AnForm.R.conePts R.D} = ∅ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«ResBridge».«interior_D» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_ResBridge_interior_D_8a07618018ce
