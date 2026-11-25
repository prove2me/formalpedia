-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LelongRegularise_mdisc_eq_zero_of_eq_zero_2c04554c731c
-- name    : P2M_GroundTheory_Heights__Heights_LelongRegularise_mdisc_eq_zero_of_eq_zero_2c04554c731c
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:27:57.96215+00:00
-- url     : https://prove2.me/theorems/3da0edf1-5e5f-490c-8318-31cdbf9de874
-- title:
--   P2 M Ground Theory Heights  Heights Lelong Regularise mdisc eq zero of eq zero 2c04554c731c: P2 M Ground Theory Heights  Heights Lelong Regularise mdisc eq zero of eq zero 2c04554c731c
-- statement:
--   The P2 M Ground Theory Heights  Heights Lelong Regularise mdisc eq zero of eq zero 2c04554c731c construction uses the P2 M Ground Theory Heights  Heights Lelong Regularise mdisc eq zero of eq zero 2c04554c731c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLelongRegularise.lean#L16-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLelongRegularise.lean#L16-L34

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongRegularise
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLelongRegularise
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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.LelongRegularise

theorem P2M_GroundTheory_Heights__Heights_LelongRegularise_mdisc_eq_zero_of_eq_zero_2c04554c731c {D : ℕ} (B : Fin (D + 1) → Matrix (Fin (D + 1)) (Fin (D + 1)) ℂ)
    (h : B 0 = 0) : ReciprocityTheory.AnForm.mdisc B = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LelongRegularise».«mdisc_eq_zero_of_eq_zero» := P2M_GroundTheory_Heights__Heights_LelongRegularise_mdisc_eq_zero_of_eq_zero_2c04554c731c
