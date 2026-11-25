-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_leviForm_gbPot_one_f3b2116693be
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_leviForm_gbPot_one_f3b2116693be
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:34:06.324774+00:00
-- url     : https://prove2.me/theorems/81a873f9-b2e8-43de-b4d1-91dfd0dab636
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Four B levi Form gb Pot one f3b2116693be: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Four B levi Form gb Pot
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Four B levi Form gb Pot one f3b2116693be construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Four B levi Form gb Pot one f3b2116693be property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/LeviFormGbPotOne.lean#L92-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/LeviFormGbPotOne.lean#L92-L102

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AMassStA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_LeviFormGbPotOne
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
open MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo
open scoped ENNReal ComplexOrder

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_leviForm_gbPot_one_f3b2116693be (z w : Fin 1 → ℂ) :
    leviForm (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbPot (D := 1)) z w =
      ((w 0).re ^ 2 + (w 0).im ^ 2) / (2 * (1 + (z 0).re ^ 2 + (z 0).im ^ 2) ^ 2) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«FourB».«leviForm_gbPot_one» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_leviForm_gbPot_one_f3b2116693be
