-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_symm
-- name    : ReciprocityTheory.ChartRestriction.G.SA.hf_symm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T03:50:54.585058+00:00
-- url     : https://prove2.me/theorems/1d316431-296e-4e0f-adec-baaa881c75c8
-- title:
--   SA: hf symm
-- statement:
--   The SA construction uses the hf symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/EichPreserves.lean#L64-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/EichPreserves.lean#L64-L75

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
variable {σ J}

theorem ReciprocityTheory.ChartRestriction.G.SA.hf_symm (hσ : ∀ x, σ (σ x) = x) (hJ : Jᵀ = J.map σ) (x y : ι → R) :
    σ (hf σ J x y) = hf σ J y x := by sorry
