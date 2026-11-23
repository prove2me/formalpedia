-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_dc_aeval_eigen
-- name    : ReciprocityTheory.ChartRestriction.DS.dc_aeval_eigen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:43:26.507774+00:00
-- url     : https://prove2.me/theorems/a5c83b39-965f-420b-8471-95ba5ed0de51
-- title:
--   DS: dc aeval eigen
-- statement:
--   The DS construction uses the dc aeval eigen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/DecompA.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/DecompA.lean#L21-L23

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

theorem ReciprocityTheory.ChartRestriction.DS.dc_aeval_eigen {T : Module.End ℂ Y} {z : ℂ} {f : Y} (hf : T f = z • f) (p : ℂ[X]) :
    aeval T p f = p.eval z • f := by sorry
