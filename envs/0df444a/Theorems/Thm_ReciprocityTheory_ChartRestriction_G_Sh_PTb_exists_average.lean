-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_exists_average
-- name    : ReciprocityTheory.ChartRestriction.G.Sh.PTb.exists_average
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:34:37.315064+00:00
-- url     : https://prove2.me/theorems/dc925659-7a03-439b-871f-8ec4b646ca97
-- title:
--   PTb: exists average
-- statement:
--   The PTb construction uses the exists average property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/GeomSumRoot.lean#L21-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/GeomSumRoot.lean#L21-L114

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_CardToMultisetEqDegree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_GeomSumRoot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh ReciprocityTheory.ChartRestriction.G.Sh.PTb
open MvPowerSeries ReciprocityTheory.PGsh
noncomputable section
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.Sh.PTb.exists_average (G : LogFGL v d) {p : ℕ} (hp : p.Prime) {ζ : C}
    (hζ : IsPrimitiveRoot ζ p) {ga : Fin d → PowerSeries C} (hga : IsCurve v ga) :
    ∃ δ : Fin d → PowerSeries C, IsCurve v δ ∧ ∀ c j, PowerSeries.coeff j (G.lgCurve δ c) =
      (p : C) * PowerSeries.coeff (p * j) (G.lgCurve ga c) := by sorry
