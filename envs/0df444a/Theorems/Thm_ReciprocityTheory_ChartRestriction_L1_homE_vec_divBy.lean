-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_homE_vec_divBy
-- name    : ReciprocityTheory.ChartRestriction.L1.homE_vec_divBy
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:45:14.226276+00:00
-- url     : https://prove2.me/theorems/58cce320-52b0-5e70-b22c-fd450777432c
-- title:
--   L1: hom E vec div By
-- statement:
--   The L1 construction uses the hom E vec div By property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/DivByPartialYAtZeroSubstAtXAtY.lean#L193-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/DivByPartialYAtZeroSubstAtXAtY.lean#L193-L201

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

theorem ReciprocityTheory.ChartRestriction.L1.homE_vec_divBy {x : K} {f h : PowerSeries K} (hfh : DivBy x (f - h)) (i : Fin 2) :
    DivByMv x (![atX f, atY f] i - ![atX h, atY h] i) := by sorry
