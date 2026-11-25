-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_PLC_zeroExt_props
-- name    : ReciprocityTheory.AnForm.M.PLC.zeroExt_props
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:21:31.966705+00:00
-- url     : https://prove2.me/theorems/c941e715-3fd1-513a-9a3b-ed244596fba6
-- title:
--   PLC: zero Ext props
-- statement:
--   The PLC construction uses the zero Ext props property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/PLCurveB.lean#L26-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/PLCurveB.lean#L26-L55

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PLCurveA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PLCurveB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff
noncomputable section
open ReciprocityTheory.AnForm.M.PLC
variable {X : Type} [TopologicalSpace X]

theorem ReciprocityTheory.AnForm.M.PLC.zeroExt_props [CompactSpace X] [T2Space X] (ψ : OpenPartialHomeomorph X (Fin 1 → ℂ))
    (v : X → ℝ) (hv : ContDiffOn ℝ ∞ (v ∘ ψ.symm) ψ.target) (hvψ : tsupport v ⊆ ψ.source) :
    ContDiff ℝ 2 (zeroExt ψ v) ∧ HasCompactSupport (zeroExt ψ v) ∧
      (∀ y ∈ ψ.target, zeroExt ψ v =ᶠ[𝓝 y] v ∘ ψ.symm) ∧
      (∀ y ∉ ψ.target, zeroExt ψ v =ᶠ[𝓝 y] 0) := by sorry
