-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointsBilinear_mixedDisc_update_sum_ae519e6d25de
-- name    : P2M_GroundTheory_Heights__Heights_PointsBilinear_mixedDisc_update_sum_ae519e6d25de
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:15:29.645082+00:00
-- url     : https://prove2.me/theorems/3129160a-b401-4225-affc-e5b09e5f67ac
-- title:
--   P2 M Ground Theory Heights  Heights Points Bilinear mixed Disc update sum ae519e6d25de: P2 M Ground Theory Heights  Heights Points Bilinear mixed Disc update sum ae519e6d25de
-- statement:
--   The P2 M Ground Theory Heights  Heights Points Bilinear mixed Disc update sum ae519e6d25de construction uses the P2 M Ground Theory Heights  Heights Points Bilinear mixed Disc update sum ae519e6d25de property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsBilinear.lean#L49-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsBilinear.lean#L49-L56

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasChainA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsBilinear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PtsIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PPtsBilinear
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo
open scoped ContDiff
open GroundTheory.Heights₂.Heights.PointsBilinear
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_PointsBilinear_mixedDisc_update_sum_ae519e6d25de {D : ℕ} {T : Type} [Fintype T] (A : Fin D → Matrix (Fin D) (Fin D) ℂ)
    (k : Fin D) (B : T → Matrix (Fin D) (Fin D) ℂ) :
    mixedDisc (Function.update A k (∑ t, B t)) = ∑ t, mixedDisc (Function.update A k (B t)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PointsBilinear».«mixedDisc_update_sum» := P2M_GroundTheory_Heights__Heights_PointsBilinear_mixedDisc_update_sum_ae519e6d25de
