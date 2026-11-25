-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_dc_aeval_mem
-- name    : ReciprocityTheory.ChartRestriction.DS.dc_aeval_mem
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T09:49:34.763796+00:00
-- url     : https://prove2.me/theorems/51be245d-3131-4fcf-88dc-74798451f911
-- title:
--   DS: dc aeval mem
-- statement:
--   The DS construction uses the dc aeval mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/DecompA.lean#L33-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/DecompA.lean#L33-L42

import Mathlib
import Definitions.Def_Lemmata_PowerApplication_PowApp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_DecompA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
variable {T : Module.End ℂ Y} {S : Submodule ℂ Y} {B : Finset ℝ}

theorem ReciprocityTheory.ChartRestriction.DS.dc_aeval_mem (hT : ∀ f ∈ S, T f ∈ S) (p : ℂ[X]) : ∀ f ∈ S, aeval T p f ∈ S := by sorry
