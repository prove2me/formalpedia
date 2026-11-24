-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_one_mem_SU
-- name    : ReciprocityTheory.ChartRestriction.G.SA.one_mem_SU
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T03:54:36.833088+00:00
-- url     : https://prove2.me/theorems/d351e458-a6aa-4c58-b038-c02829eaae13
-- title:
--   SA: one mem SU
-- statement:
--   The SA construction uses the one mem SU property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/EichPreserves.lean#L116-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/EichPreserves.lean#L116-L117

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

theorem ReciprocityTheory.ChartRestriction.G.SA.one_mem_SU : (1 : Matrix ι ι R) ∈ SU σ J := by sorry
