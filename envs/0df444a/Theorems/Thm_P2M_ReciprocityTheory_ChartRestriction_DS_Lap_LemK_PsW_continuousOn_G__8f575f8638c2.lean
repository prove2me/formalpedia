-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_PsW_continuousOn_G__8f575f8638c2
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_PsW_continuousOn_G__8f575f8638c2
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:12:29.065525+00:00
-- url     : https://prove2.me/theorems/471c2a13-144c-438f-9181-d7c0930f0755
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS Lap Lem K Ps W continuous On G  8f575f8638c2: P2 M Reciprocity Theory Chart Restriction DS Lap Lem K Ps W continuous On G  8f575f8638c2
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS Lap Lem K Ps W continuous On G  8f575f8638c2 construction uses the P2 M Reciprocity Theory Chart Restriction DS Lap Lem K Ps W continuous On G  8f575f8638c2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/KTypeLemma/PsWord.lean#L178-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/KTypeLemma/PsWord.lean#L178-L201

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

theorem P2M_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_PsW_continuousOn_G__8f575f8638c2 (T : KType ε Λ) (μ : Fin n → ℤ) (D : List MM) :
    ContinuousOn (fun p : 𝕄 × KG ε => G' T μ D p.1 p.2) (Ps1.Uset ε ×ˢ Set.univ) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«Lap».«LemK».«PsW».«continuousOn_G'» := P2M_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_PsW_continuousOn_G__8f575f8638c2
