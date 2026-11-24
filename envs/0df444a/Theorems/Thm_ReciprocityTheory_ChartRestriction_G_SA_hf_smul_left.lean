-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_smul_left
-- name    : ReciprocityTheory.ChartRestriction.G.SA.hf_smul_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T03:50:56.220415+00:00
-- url     : https://prove2.me/theorems/f30dddf9-c6e1-498d-ada3-82dcf256f663
-- title:
--   SA: hf smul left
-- statement:
--   The SA construction uses the hf smul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/EichPreserves.lean#L23-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/EichPreserves.lean#L23-L27

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_SAOpenStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichPreserves
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.SA
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R] (σ : R →+* R)
  (J : Matrix ι ι R)

theorem ReciprocityTheory.ChartRestriction.G.SA.hf_smul_left (a : R) (x y : ι → R) : hf σ J (a • x) y = a * hf σ J x y := by sorry
