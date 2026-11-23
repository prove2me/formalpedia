-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_dc_injOn_id_cplx
-- name    : ReciprocityTheory.ChartRestriction.DS.dc_injOn_id_cplx
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:10:27.154588+00:00
-- url     : https://prove2.me/theorems/342af1e7-2c95-433b-9a32-5bcd1963cba5
-- title:
--   DS: dc inj On id cplx
-- statement:
--   The DS construction uses the dc inj On id cplx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/DecompA.lean#L15-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/DecompA.lean#L15-L16

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

theorem ReciprocityTheory.ChartRestriction.DS.dc_injOn_id_cplx (B : Finset ℝ) : Set.InjOn (id : ℂ → ℂ) (dc_cplxPts B : Set ℂ) := by sorry
