-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_regMax_subtype_16df40b114c4
-- name    : P2M_GroundTheory_Heights__Heights_Regular_regMax_subtype_16df40b114c4
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:18:46.492147+00:00
-- url     : https://prove2.me/theorems/7dc96e72-71b0-4e77-a245-a52b085df0c8
-- title:
--   P2 M Ground Theory Heights  Heights Regular reg Max subtype 16df40b114c4: P2 M Ground Theory Heights  Heights Regular reg Max subtype 16df40b114c4
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular reg Max subtype 16df40b114c4 construction uses the P2 M Ground Theory Heights  Heights Regular reg Max subtype 16df40b114c4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/RegMaxReindex.lean#L54-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/RegMaxReindex.lean#L54-L111

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_RegMaxReindex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open MeasureTheory
open ReciprocityTheory.AnForm.A (regMax tmax kθ)
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Regular_regMax_subtype_16df40b114c4 {ι : Type} [Fintype ι] [Nonempty ι] (p : ι → Prop) [DecidablePred p]
    [Nonempty {i // p i}] {η : ℝ} (hη : 0 ≤ η) (t : ι → ℝ)
    (hdom : ∀ i, ¬ p i → ∃ k, p k ∧ t i + η ≤ t k) :
    regMax η t = regMax η (fun k : {i // p i} => t k) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«regMax_subtype» := P2M_GroundTheory_Heights__Heights_Regular_regMax_subtype_16df40b114c4
