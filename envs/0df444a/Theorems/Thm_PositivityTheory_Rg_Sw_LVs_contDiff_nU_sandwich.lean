-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_contDiff_nU_sandwich
-- name    : PositivityTheory.Rg.Sw.LVs.contDiff_nU_sandwich
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:05:26.517041+00:00
-- url     : https://prove2.me/theorems/4d5a7140-a2e0-4824-87b1-541c60440850
-- title:
--   LVs: cont Diff n U sandwich
-- statement:
--   The LVs construction uses the cont Diff n U sandwich property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/IteratedFDerivMulConstOf.lean#L136-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/IteratedFDerivMulConstOf.lean#L136-L155

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ContinuousOnIteratedFDerivTranslate
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_IteratedFDerivMulConstOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.LVs.contDiff_nU_sandwich (a b : M2 n) : ContDiff ℂ ∞ (fun H : Matrix (Fin n) (Fin n) ℂ => a * nU H * b) := by sorry
