-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_closure_inv
-- name    : ReciprocityTheory.ChartRestriction.G.SA.closure_inv
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:33:17.32118+00:00
-- url     : https://prove2.me/theorems/6085067a-0232-4f4b-9234-21eb03f778bb
-- title:
--   SA: closure inv
-- statement:
--   The SA construction uses the closure inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/EichAlongSub.lean#L92-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/EichAlongSub.lean#L92-L107

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

theorem ReciprocityTheory.ChartRestriction.G.SA.closure_inv {M : Matrix ι ι R} (hM : M ∈ Submonoid.closure (eichSet σ J e f)) :
    ∃ M' ∈ Submonoid.closure (eichSet σ J e f), M' * M = 1 ∧ M * M' = 1 := by sorry
