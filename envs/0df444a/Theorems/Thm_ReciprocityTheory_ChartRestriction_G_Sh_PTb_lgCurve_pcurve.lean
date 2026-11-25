-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_lgCurve_pcurve
-- name    : ReciprocityTheory.ChartRestriction.G.Sh.PTb.lgCurve_pcurve
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:35:00.800197+00:00
-- url     : https://prove2.me/theorems/5646fff7-5728-5090-9f78-5acf42af56e6
-- title:
--   PTb: lg Curve pcurve
-- statement:
--   The PTb construction uses the lg Curve pcurve property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/LgCurvePcurve.lean#L264-L280
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/LgCurvePcurve.lean#L264-L280

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_CardToMultisetEqDegree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_EqZeroOfVecMulTmat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_LgCurvePcurve
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

theorem ReciprocityTheory.ChartRestriction.G.Sh.PTb.lgCurve_pcurve (G : LogFGL v d) {p : ℕ} (hp : p ≠ 0) {γ : Fin d → Fin d → PowerSeries C}
    (hγ : ∀ a, IsCurve v (γ a)) (x : ℕ → Fin d → C) :
    ∀ n, (∀ s < n, ∀ b, IsIntV v (x s b)) → ∀ a, G.lgCurve (pcurve G p γ x n) a =
      ∑ s ∈ Finset.range n, ∑ b, PowerSeries.expand (p ^ s) (pow_ne_zero _ hp)
        (PowerSeries.rescale (x s b) (G.lgCurve (γ b) a))
  := by sorry
