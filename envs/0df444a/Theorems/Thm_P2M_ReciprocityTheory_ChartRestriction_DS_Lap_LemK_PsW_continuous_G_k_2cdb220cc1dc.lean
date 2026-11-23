-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_PsW_continuous_G_k_2cdb220cc1dc
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_PsW_continuous_G_k_2cdb220cc1dc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:12:35.097103+00:00
-- url     : https://prove2.me/theorems/d579fd62-55eb-4294-8a48-1a917bd4ce21
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS Lap Lem K Ps W continuous G k 2cdb220cc1dc: P2 M Reciprocity Theory Chart Restriction DS Lap Lem K Ps W continuous G k 2cdb220cc1dc
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS Lap Lem K Ps W continuous G k 2cdb220cc1dc construction uses the P2 M Reciprocity Theory Chart Restriction DS Lap Lem K Ps W continuous G k 2cdb220cc1dc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/KTypeLemma/PsWord.lean#L218-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/KTypeLemma/PsWord.lean#L218-L242

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_PsWord
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix Topology
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.LemK
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open ReciprocityTheory.ChartRestriction.DS.Lap.LemK.PsW
variable {n : ℕ}
local notation "𝕄" => Fin n → Fin n → ℂ
local notation "MM" => Matrix (Fin n) (Fin n) ℂ
local notation "WW" => ((Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ)) × (Fin n → Fin n → ℂ)
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}

theorem P2M_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_PsW_continuous_G_k_2cdb220cc1dc (T : KType ε Λ) (μ : Fin n → ℤ) (D : List MM) {z : 𝕄} (hz : z ∈ Ps1.Uset ε) :
    Continuous (G' T μ D z) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«Lap».«LemK».«PsW».«continuous_G'k» := P2M_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_PsW_continuous_G_k_2cdb220cc1dc
