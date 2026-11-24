-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_eichAlong_sub
-- name    : ReciprocityTheory.ChartRestriction.G.SA.eichAlong_sub
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:06:27.306089+00:00
-- url     : https://prove2.me/theorems/0385db5c-d944-4994-b95a-0fc75900b63a
-- title:
--   SA: eich Along sub
-- statement:
--   The SA construction uses the eich Along sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/EichAlongSub.lean#L55-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/EichAlongSub.lean#L55-L59

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichPreserves
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichAlongSub
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
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R] {σ : R →+* R}
  {J : Matrix ι ι R}
variable (hσ : ∀ x, σ (σ x) = x) (hJ : Jᵀ = J.map σ)
include hσ hJ

theorem ReciprocityTheory.ChartRestriction.G.SA.eichAlong_sub {e f : ι → R} (he : hf σ J e e = 0) : eichAlong σ J e f ⊆ SU σ J := by sorry
