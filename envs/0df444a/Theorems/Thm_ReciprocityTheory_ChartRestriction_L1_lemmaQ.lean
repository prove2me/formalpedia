-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_lemmaQ
-- name    : ReciprocityTheory.ChartRestriction.L1.lemmaQ
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:45:18.951798+00:00
-- url     : https://prove2.me/theorems/89f47304-7a4a-47fd-98cd-d80be203f044
-- title:
--   L1: lemma Q
-- statement:
--   The L1 construction uses the lemma Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonD.lean#L195-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonD.lean#L195-L232

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonD
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
variable {lam : PowerSeries K} {Φ : MvPowerSeries (Fin 2) K} {A : PowerSeries K} {a : K}

theorem ReciprocityTheory.ChartRestriction.L1.lemmaQ (hF : FrobField K l σ) (h : HD σ lam Φ A a) {D : PowerSeries K}
    (hD : QCls l Φ A a D) :
    ∃ Dp : PowerSeries K,
      QCls l (MvPowerSeries.map (σ.comp σ) Φ) (PowerSeries.map (σ.comp σ) A) a Dp ∧
      DivBy (l : K) (D - C (coeff 1 D) * lam - Dp.subst ((X : PowerSeries K) ^ (l ^ 2))) := by sorry
