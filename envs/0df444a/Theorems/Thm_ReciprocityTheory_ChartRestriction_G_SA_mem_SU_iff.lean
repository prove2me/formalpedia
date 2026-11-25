-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_mem_SU_iff
-- name    : ReciprocityTheory.ChartRestriction.G.SA.mem_SU_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:56.197821+00:00
-- url     : https://prove2.me/theorems/5f74fb1a-1989-4974-b285-c5fc0eb71c40
-- title:
--   SA: mem SU iff
-- statement:
--   The SA construction uses the mem SU iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/EichPreserves.lean#L104-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/EichPreserves.lean#L104-L110

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

theorem ReciprocityTheory.ChartRestriction.G.SA.mem_SU_iff (g : Matrix ι ι R) :
    g ∈ SU σ J ↔ g.det = 1 ∧ ∀ x y, hf σ J (g *ᵥ x) (g *ᵥ y) = hf σ J x y := by sorry
