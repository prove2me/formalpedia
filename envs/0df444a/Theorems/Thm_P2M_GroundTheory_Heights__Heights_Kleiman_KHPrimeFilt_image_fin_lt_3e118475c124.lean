-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHPrimeFilt_image_fin_lt_3e118475c124
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_KHPrimeFilt_image_fin_lt_3e118475c124
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:27:02.049678+00:00
-- url     : https://prove2.me/theorems/02c981b6-fd37-458c-a882-e101ef6a9497
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman KHPrime Filt image fin lt 3e118475c124: P2 M Ground Theory Heights  Heights Kleiman KHPrime Filt image fin lt 3e118475c124
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman KHPrime Filt image fin lt 3e118475c124 construction uses the P2 M Ground Theory Heights  Heights Kleiman KHPrime Filt image fin lt 3e118475c124 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHPrimeFilt.lean#L245-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHPrimeFilt.lean#L245-L252

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgFiltSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PKHPrimeFilt
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH
open GroundTheory.Heights₂.Heights.Kleiman.KHPrimeFilt

theorem P2M_GroundTheory_Heights__Heights_Kleiman_KHPrimeFilt_image_fin_lt_3e118475c124 {M : Type} {r : ℕ} (f : ℕ → M) (j : Fin r) :
    (fun l : Fin r => f l) '' {l | l < j} = f '' {l : ℕ | l < j} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«KHPrimeFilt».«image_fin_lt» := P2M_GroundTheory_Heights__Heights_Kleiman_KHPrimeFilt_image_fin_lt_3e118475c124
