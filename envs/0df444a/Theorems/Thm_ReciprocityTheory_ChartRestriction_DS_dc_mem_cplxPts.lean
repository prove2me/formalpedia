-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_dc_mem_cplxPts
-- name    : ReciprocityTheory.ChartRestriction.DS.dc_mem_cplxPts
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T00:43:26.001866+00:00
-- url     : https://prove2.me/theorems/d44b0e3f-e203-431b-ad1c-49804343e6d9
-- title:
--   DS: dc mem cplx Pts
-- statement:
--   The DS construction uses the dc mem cplx Pts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/DecompA.lean#L18-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/DecompA.lean#L18-L19

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

theorem ReciprocityTheory.ChartRestriction.DS.dc_mem_cplxPts {B : Finset ℝ} {z : ℂ} : z ∈ dc_cplxPts B ↔ ∃ b ∈ B, (b : ℂ) = z := by sorry
