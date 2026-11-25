-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_homE_expand_subst_map_congr
-- name    : ReciprocityTheory.ChartRestriction.L1.homE_expand_subst_map_congr
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:45:05.989163+00:00
-- url     : https://prove2.me/theorems/c6f5e9a1-5f8c-4241-bde9-bd31a65e9b15
-- title:
--   L1: hom E expand subst map congr
-- statement:
--   The L1 construction uses the hom E expand subst map congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/DivByPartialYAtZeroSubstAtXAtY.lean#L146-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/DivByPartialYAtZeroSubstAtXAtY.lean#L146-L176

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_DivByPartialYAtZeroSubstAtXAtY
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ} {σ : K →+* K}
variable {lam₁ lam₂ : PowerSeries K} {Φ₁ Φ₂ : MvPowerSeries (Fin 2) K} {A₁ A₂ g : PowerSeries K}

theorem ReciprocityTheory.ChartRestriction.L1.homE_expand_subst_map_congr {ι : Type} (hF : FrobField K l σ) {g₁ : PowerSeries K}
    (hg₁ : IntegralPS g₁) (hc : DivBy (l : K) (g - g₁.subst ((X : PowerSeries K) ^ l)))
    (P : MvPowerSeries ι K) (hP0 : MvPowerSeries.constantCoeff P = 0) (hP : IntegralMv P) :
    DivByMv (l : K) (MvPowerSeries.expand l hF.prime.ne_zero (g₁.subst (MvPowerSeries.map σ P))
      - g.subst P) := by sorry
