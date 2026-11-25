-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_hom_desc
-- name    : ReciprocityTheory.ChartRestriction.L1.hom_desc
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:44:20.334237+00:00
-- url     : https://prove2.me/theorems/a2eb9528-ab34-4917-b23f-c22a5c879414
-- title:
--   L1: hom desc
-- statement:
--   The L1 construction uses the hom desc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/DivByPartialYAtZeroSubstAtXAtY.lean#L211-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/DivByPartialYAtZeroSubstAtXAtY.lean#L211-L264

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

theorem ReciprocityTheory.ChartRestriction.L1.hom_desc (hF : FrobField K l σ) (hΦ₁0 : MvPowerSeries.constantCoeff Φ₁ = 0)
    (hΦ₁ : IntegralMv Φ₁) (hΦ₂0 : MvPowerSeries.constantCoeff Φ₂ = 0) (hΦ₂ : IntegralMv Φ₂)
    (hA₁0 : constantCoeff A₁ = 0) (hA₁ : IntegralPS A₁) (hA₂0 : constantCoeff A₂ = 0)
    (hA₂ : IntegralPS A₂) (hg : HomCls l Φ₁ A₁ Φ₂ A₂ g) (hg' : DivBy (l : K) (derivative K g)) :
    DivBy (l : K) (g - (desc l g).subst ((X : PowerSeries K) ^ l)) ∧
      HomCls l (MvPowerSeries.map σ Φ₁) (PowerSeries.map σ A₁) Φ₂ A₂ (desc l g) := by sorry
