-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_desc_QCls
-- name    : ReciprocityTheory.ChartRestriction.L1.desc_QCls
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:44:37.663185+00:00
-- url     : https://prove2.me/theorems/6f19208c-b14b-5f38-989a-f3ca34d8ff44
-- title:
--   L1: desc QCls
-- statement:
--   The L1 construction uses the desc QCls property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonC.lean#L119-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonC.lean#L119-L148

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonC
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

theorem ReciprocityTheory.ChartRestriction.L1.desc_QCls (hF : FrobField K l σ) {Φ : MvPowerSeries (Fin 2) K} {A : PowerSeries K} {b : K}
    (hΦ0 : MvPowerSeries.constantCoeff Φ = 0) (hΦ : IntegralMv Φ) (hA0 : constantCoeff A = 0)
    (hA : IntegralPS A) (hb : ‖b‖ ≤ 1) {D : PowerSeries K} (hD : QCls l Φ A b D)
    (hD' : DivBy (l : K) (derivative K D)) :
    QCls l (MvPowerSeries.map σ Φ) (PowerSeries.map σ A) b (desc l D) := by sorry
