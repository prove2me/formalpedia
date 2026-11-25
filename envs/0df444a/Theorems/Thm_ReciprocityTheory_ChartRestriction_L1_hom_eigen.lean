-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_hom_eigen
-- name    : ReciprocityTheory.ChartRestriction.L1.hom_eigen
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:51:25.07929+00:00
-- url     : https://prove2.me/theorems/ee7d4ba2-f570-5aab-861e-c578a3746fba
-- title:
--   L1: hom eigen
-- statement:
--   The L1 construction uses the hom eigen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/DivByPartialYAtZeroSubstAtXAtY.lean#L134-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/DivByPartialYAtZeroSubstAtXAtY.lean#L134-L144

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

theorem ReciprocityTheory.ChartRestriction.L1.hom_eigen (hA₁ : constantCoeff A₁ = 0) (hA₂ : constantCoeff A₂ = 0)
    (hg : HomCls l Φ₁ A₁ Φ₂ A₂ g) (h : ‖coeff 1 A₁ - coeff 1 A₂‖ = 1) :
    ‖coeff 1 g‖ ≤ ‖(l : K)‖ := by sorry
