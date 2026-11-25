-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_norm_le_lintegral_ray_iteratedFDeriv__727993c96453
-- name    : P2M_GlobalTheory_T_norm_le_lintegral_ray_iteratedFDeriv__727993c96453
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:10:33.847207+00:00
-- url     : https://prove2.me/theorems/00f03298-b079-4692-a722-a34509747f80
-- title:
--   P2 M Global Theory T norm le lintegral ray iterated FDeriv  727993c96453: P2 M Global Theory T norm le lintegral ray iterated FDeriv  727993c96453
-- statement:
--   The P2 M Global Theory T norm le lintegral ray iterated FDeriv  727993c96453 construction uses the P2 M Global Theory T norm le lintegral ray iterated FDeriv  727993c96453 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormLeLintegralRayIteratedFDerivStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormLeLintegralRayIteratedFDerivStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormLeLintegralRayIteratedFDeriv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormLeLintegralRayIteratedFDerivStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Set Module
open scoped ENNReal
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_norm_le_lintegral_ray_iteratedFDeriv__727993c96453 : ∀ {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (G : E → F) (m : ℕ) (x v : E), ContDiff ℝ (⊤ : ℕ∞) G → (∀ j ≤ m, Tendsto (fun t : ℝ => iteratedFDeriv ℝ j G (x + t • v)) atTop (𝓝 0)) → ENNReal.ofReal ‖G x‖ ≤ ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ m / (m.factorial : ℝ) * (‖v‖ ^ (m + 1) * ‖iteratedFDeriv ℝ (m + 1) G (x + t • v)‖)) := by sorry

alias «GlobalTheory».«T».«norm_le_lintegral_ray_iteratedFDeriv'» := P2M_GlobalTheory_T_norm_le_lintegral_ray_iteratedFDeriv__727993c96453
