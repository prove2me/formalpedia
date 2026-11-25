-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_conj_closure
-- name    : ReciprocityTheory.ChartRestriction.G.SA.conj_closure
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:37:20.080166+00:00
-- url     : https://prove2.me/theorems/2595b188-f611-530e-8ee5-590fa9ce3e37
-- title:
--   SA: conj closure
-- statement:
--   The SA construction uses the conj closure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/ConjMemEichSet.lean#L56-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/ConjMemEichSet.lean#L56-L68

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_UnitaryTransvectionZeroSecondMemClosure
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_ConjMemEichSet
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
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] {σ : K →+* K}
  {J : Matrix ι ι K}
variable (hσ : ∀ x, σ (σ x) = x) (hJ : Jᵀ = J.map σ)
include hσ hJ
variable {e f : ι → K} (he : hf σ J e e = 0) (hff : hf σ J f f = 0) (hef : hf σ J e f = 1)
include he hff hef

theorem ReciprocityTheory.ChartRestriction.G.SA.conj_closure {l m : K} (hml : m * σ l = 1) {n : Matrix ι ι K}
    (hn : n ∈ Submonoid.closure (eichSet σ J e f)) :
    ∃ n' ∈ Submonoid.closure (eichSet σ J e f), tor σ J e f l m * n = n' * tor σ J e f l m := by sorry
