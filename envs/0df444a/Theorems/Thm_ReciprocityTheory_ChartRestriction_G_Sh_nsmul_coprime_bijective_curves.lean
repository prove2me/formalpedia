-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_nsmul_coprime_bijective_curves
-- name    : ReciprocityTheory.ChartRestriction.G.Sh.nsmul_coprime_bijective_curves
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:35:31.575082+00:00
-- url     : https://prove2.me/theorems/9fd1c031-6e2b-5ea1-b231-065c5fa52349
-- title:
--   Sh: nsmul coprime bijective curves
-- statement:
--   The Sh construction uses the nsmul coprime bijective curves property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/NsmulCoprimeBijectiveCurves.lean#L129-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/NsmulCoprimeBijectiveCurves.lean#L129-L204

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtSolveMapFixedIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_NsmulCoprimeBijectiveCurves
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh
open MvPowerSeries ReciprocityTheory.PGsh
open Classical
noncomputable section
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.Sh.nsmul_coprime_bijective_curves [CharZero C] (G : LogFGL v d) {p : ℕ} (hp : p.Prime) (hvp : v (p : C) = 1)
    (n : ℕ) (hn : ¬ p ∣ n) (gb : Fin d → PowerSeries C) (hgb : IsCurve v gb) :
    ∃! ga : Fin d → PowerSeries C, IsCurve v ga ∧ G.nsmulF n ga = gb := by sorry
