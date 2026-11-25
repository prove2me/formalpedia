-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_eichSet_sub
-- name    : ReciprocityTheory.ChartRestriction.G.SA.eichSet_sub
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:37:29.25312+00:00
-- url     : https://prove2.me/theorems/d3289b0a-f89f-4f63-abdd-eacb2a80f328
-- title:
--   SA: eich Set sub
-- statement:
--   The SA construction uses the eich Set sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/EichAlongSub.lean#L76-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/EichAlongSub.lean#L76-L77

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
variable {e f : ι → R} (he : hf σ J e e = 0) (hff : hf σ J f f = 0)
include he hff

theorem ReciprocityTheory.ChartRestriction.G.SA.eichSet_sub : eichSet σ J e f ⊆ SU σ J := by sorry
