-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_AnForm_M_degree_local_sheets__daf628801bfb
-- name    : P2M_ReciprocityTheory_AnForm_M_degree_local_sheets__daf628801bfb
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:43:40.271198+00:00
-- url     : https://prove2.me/theorems/c03be8a1-7c35-5a5d-9cff-c1d0638bc7b3
-- title:
--   P2 M Reciprocity Theory An Form M degree local sheets  daf628801bfb: P2 M Reciprocity Theory An Form M degree local sheets  daf628801bfb
-- statement:
--   The P2 M Reciprocity Theory An Form M degree local sheets  daf628801bfb construction uses the P2 M Reciprocity Theory An Form M degree local sheets  daf628801bfb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/DegreeSheets.lean#L96-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/DegreeSheets.lean#L96-L177

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Pullback
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_AnalyticSubsetChartLocal
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_DegreeSheets
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open FinHolAtlas Topology
noncomputable section
variable {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem P2M_ReciprocityTheory_AnForm_M_degree_local_sheets__daf628801bfb [CompactSpace Y] [T2Space Y] [T2Space X]
    {A : FinHolAtlas e X} {B : FinHolAtlas e Y} {h : Y → X} (hh : HoloMap B A h) {d : ℕ}
    {S : Set X} (hd : IsDegreeOff A B h d S) (x : X) (hx : x ∉ S) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ Disjoint V S ∧ ∃ k : Fin A.n, V ⊆ (A.chart k).source ∧
      ∃ W : Fin d → Set Y, (∀ i, IsOpen (W i)) ∧ Pairwise (Function.onFun Disjoint W) ∧
        h ⁻¹' V = ⋃ i, W i ∧ ∀ i, Set.BijOn h (W i) V ∧
          ∃ j : Fin B.n, W i ⊆ (B.chart j).source := by sorry

alias «ReciprocityTheory».«AnForm».«M».«degree_local_sheets'» := P2M_ReciprocityTheory_AnForm_M_degree_local_sheets__daf628801bfb
