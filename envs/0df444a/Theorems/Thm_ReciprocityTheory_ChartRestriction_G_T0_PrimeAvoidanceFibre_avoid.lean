-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_PrimeAvoidanceFibre_avoid
-- name    : ReciprocityTheory.ChartRestriction.G.T0.PrimeAvoidanceFibre.avoid
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:02:56.967784+00:00
-- url     : https://prove2.me/theorems/b84d7f9a-1a51-4cf6-a7e1-7c622e1def41
-- title:
--   Prime Avoidance Fibre: avoid
-- statement:
--   The Prime Avoidance Fibre construction uses the avoid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/PrimeAvoidanceFibre.lean#L7-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/PrimeAvoidanceFibre.lean#L7-L45

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SpanTopOfComplete
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_PrimeAvoidanceFibre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.PrimeAvoidanceFibre
open IsLocalRing

theorem ReciprocityTheory.ChartRestriction.G.T0.PrimeAvoidanceFibre.avoid {B : Type*} [CommRing B] [IsNoetherianRing B] (M q : Ideal B) [hM : M.IsMaximal] (w : B)
    (hchain : ∀ P : Ideal B, P.IsPrime → q ≤ P → P ≤ M → w ∈ P → P = M) :
    ∃ s ∉ M, ∀ P : Ideal B, P.IsPrime → q ≤ P → w ∈ P → s ∉ P → P = M := by sorry
