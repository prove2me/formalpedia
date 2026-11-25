-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_hom_deriv
-- name    : ReciprocityTheory.ChartRestriction.L1.hom_deriv
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:44:53.245716+00:00
-- url     : https://prove2.me/theorems/b60c825f-1af2-4336-908a-591677cef6ea
-- title:
--   L1: hom deriv
-- statement:
--   The L1 construction uses the hom deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/DivByPartialYAtZeroSubstAtXAtY.lean#L105-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/DivByPartialYAtZeroSubstAtXAtY.lean#L105-L132

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

theorem ReciprocityTheory.ChartRestriction.L1.hom_deriv (hl1 : ‖(l : K)‖ ≤ 1) (h₁ : LawD lam₁ Φ₁) (h₂ : LawD lam₂ Φ₂)
    (hg : HomCls l Φ₁ A₁ Φ₂ A₂ g) (h0 : ‖coeff 1 g‖ ≤ ‖(l : K)‖) :
    DivBy (l : K) (derivative K g) := by sorry
