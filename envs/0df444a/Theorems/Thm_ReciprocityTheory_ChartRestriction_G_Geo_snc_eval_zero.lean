-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_snc_eval_zero
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.snc_eval_zero
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:26:43.050806+00:00
-- url     : https://prove2.me/theorems/dc81f3d0-f0b5-4980-a6eb-0048b5355286
-- title:
--   Geo: snc eval zero
-- statement:
--   The Geo construction uses the snc eval zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterDivPushB.lean#L10-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterDivPushB.lean#L10-L20

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivPushA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_SNCAtlas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivPushB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M

theorem ReciprocityTheory.ChartRestriction.G.Geo.snc_eval_zero {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}
    {L : LocPot X} {s : X → X → ℂ} {r : ℕ} {m : Fin r → ℕ} {W : Fin r → Set X}
    (h : IsSNC A L s m W) {k : Fin r} {x : X} (hx : x ∈ W k) (hm : m k ≠ 0) : s x x = 0 := by sorry
