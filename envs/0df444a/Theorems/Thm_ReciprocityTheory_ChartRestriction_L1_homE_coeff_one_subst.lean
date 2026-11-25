-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_homE_coeff_one_subst
-- name    : ReciprocityTheory.ChartRestriction.L1.homE_coeff_one_subst
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:44:08.374901+00:00
-- url     : https://prove2.me/theorems/1741d02f-6584-4758-ad37-702337834948
-- title:
--   L1: hom E coeff one subst
-- statement:
--   The L1 construction uses the hom E coeff one subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/DivByPartialYAtZeroSubstAtXAtY.lean#L14-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/DivByPartialYAtZeroSubstAtXAtY.lean#L14-L27

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

theorem ReciprocityTheory.ChartRestriction.L1.homE_coeff_one_subst {R : Type} [CommRing R] (f a : PowerSeries R) (ha : constantCoeff a = 0) :
    coeff 1 (f.subst a) = coeff 1 f * coeff 1 a := by sorry
