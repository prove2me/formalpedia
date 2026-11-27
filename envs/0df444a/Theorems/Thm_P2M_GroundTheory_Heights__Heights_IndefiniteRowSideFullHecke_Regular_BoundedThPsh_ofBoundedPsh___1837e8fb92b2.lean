-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_BoundedThPsh_ofBoundedPsh___1837e8fb92b2
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_BoundedThPsh_ofBoundedPsh___1837e8fb92b2
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:07:41.935103+00:00
-- url     : https://prove2.me/theorems/8739c57a-3b98-5627-bac2-5047ccf4f2bf
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular Bounded Th Psh of Bounded Psh   1837e8fb92b2: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular Boun
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular Bounded Th Psh of Bounded Psh   1837e8fb92b2 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Regular Bounded Th Psh of Bounded Psh   1837e8fb92b2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/ProjLineChartsNotSubsetBall.lean#L141-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/ProjLineChartsNotSubsetBall.lean#L141-L143

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_ToPotentialChartsChartFun
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_ProjLineChartsNotSubsetBall
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
open MeasureTheory Metric Set
open scoped ContDiff
open ReciprocityTheory.AnForm.A (Mollifier molli regMax coordDiv limsupExt)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPosPot)
open GroundTheory.Heights₂.Heights.Regular (PotentialCharts BoundedPshData pointReg pointCharts pointAtlas)
local notation "RegChartDataA" => GroundTheory.Heights₂.Heights.Regular.RegChartData
noncomputable section
variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X}
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.BoundedThPsh

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_BoundedThPsh_ofBoundedPsh___1837e8fb92b2 [CompactSpace X] (P : BoundedPshData A) (om : LocPot X)
    (om_pot : IsPotential A om) (om_pos : IsPosPot A om) :
    (ofBoundedPsh P om om_pot om_pos).φ = P.ph := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Regular».«BoundedThPsh».«ofBoundedPsh_φ» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_BoundedThPsh_ofBoundedPsh___1837e8fb92b2
