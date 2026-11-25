-- Prove2me | Theorems.Thm_P2M_GlobalTheory_LeviZero_leviV_sum__12cf4af592ec
-- name    : P2M_GlobalTheory_LeviZero_leviV_sum__12cf4af592ec
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:37:21.719714+00:00
-- url     : https://prove2.me/theorems/02bf22fc-9696-569a-8c85-06143e478de8
-- title:
--   P2 M Global Theory Levi Zero levi V sum  12cf4af592ec: P2 M Global Theory Levi Zero levi V sum  12cf4af592ec
-- statement:
--   The P2 M Global Theory Levi Zero levi V sum  12cf4af592ec construction uses the P2 M Global Theory Levi Zero levi V sum  12cf4af592ec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/LeviFormWeightMetricOrthonormalDiagonal.lean#L266-L276
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/LeviFormWeightMetricOrthonormalDiagonal.lean#L266-L276

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LeviFormWeightMetricOrthonormalDiagonal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.LeviZero
open Filter
open scoped ComplexConjugate
noncomputable section
variable {n : ℕ} {ξ : Fin n → ℂ} {x : V n}

theorem P2M_GlobalTheory_LeviZero_leviV_sum__12cf4af592ec {ι : Type*} (s : Finset ι) {f : ι → V n → ℂ}
    (h : ∀ i ∈ s, ContDiffAt ℝ 2 (f i) x) :
    leviV n (fun y => ∑ i ∈ s, f i y) x ξ = ∑ i ∈ s, leviV n (f i) x ξ := by sorry

alias «GlobalTheory».«LeviZero».«leviV_sum'» := P2M_GlobalTheory_LeviZero_leviV_sum__12cf4af592ec
