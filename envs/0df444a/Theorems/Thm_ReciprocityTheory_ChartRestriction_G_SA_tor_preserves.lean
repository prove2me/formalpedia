-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_tor_preserves
-- name    : ReciprocityTheory.ChartRestriction.G.SA.tor_preserves
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:35:16.430441+00:00
-- url     : https://prove2.me/theorems/fc73ad60-86ac-48ca-81ac-6ea251aac732
-- title:
--   SA: tor preserves
-- statement:
--   The SA construction uses the tor preserves property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/EichAlongSub.lean#L115-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/EichAlongSub.lean#L115-L124

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
variable (hef : hf σ J e f = 1)
include hef

theorem ReciprocityTheory.ChartRestriction.G.SA.tor_preserves {l m : R} (hlm : m * σ l = 1) (x y : ι → R) :
    hf σ J (tor σ J e f l m *ᵥ x) (tor σ J e f l m *ᵥ y) = hf σ J x y := by sorry
