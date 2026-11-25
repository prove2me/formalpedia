-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LelongRegularise_maDens_eq_zero_of_eventually_fd74858b873d
-- name    : P2M_GroundTheory_Heights__Heights_LelongRegularise_maDens_eq_zero_of_eventually_fd74858b873d
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:28:48.595521+00:00
-- url     : https://prove2.me/theorems/ab8fe5bf-0ff1-4a53-a7e8-3b32fab238d0
-- title:
--   P2 M Ground Theory Heights  Heights Lelong Regularise ma Dens eq zero of eventually fd74858b873d: P2 M Ground Theory Heights  Heights Lelong Regularise ma Dens eq zero of eventually fd74858b873d
-- statement:
--   The P2 M Ground Theory Heights  Heights Lelong Regularise ma Dens eq zero of eventually fd74858b873d construction uses the P2 M Ground Theory Heights  Heights Lelong Regularise ma Dens eq zero of eventually fd74858b873d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLelongRegularise.lean#L36-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLelongRegularise.lean#L36-L46

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

theorem P2M_GroundTheory_Heights__Heights_LelongRegularise_maDens_eq_zero_of_eventually_fd74858b873d {D : ℕ} (F : Fin (D + 1) → (Fin (D + 1) → ℂ) → ℝ)
    {y : Fin (D + 1) → ℂ} (h : F 0 =ᶠ[𝓝 y] fun _ => 0) : ReciprocityTheory.AnForm.maDens F y = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LelongRegularise».«maDens_eq_zero_of_eventually» := P2M_GroundTheory_Heights__Heights_LelongRegularise_maDens_eq_zero_of_eventually_fd74858b873d
