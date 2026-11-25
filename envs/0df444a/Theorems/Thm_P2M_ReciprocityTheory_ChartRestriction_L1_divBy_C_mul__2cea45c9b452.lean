-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_L1_divBy_C_mul__2cea45c9b452
-- name    : P2M_ReciprocityTheory_ChartRestriction_L1_divBy_C_mul__2cea45c9b452
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:17:56.153971+00:00
-- url     : https://prove2.me/theorems/501c8709-20cf-4f2a-9bc0-32c23fd0db41
-- title:
--   P2 M Reciprocity Theory Chart Restriction L1 div By C mul  2cea45c9b452: P2 M Reciprocity Theory Chart Restriction L1 div By C mul  2cea45c9b452
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction L1 div By C mul  2cea45c9b452 construction uses the P2 M Reciprocity Theory Chart Restriction L1 div By C mul  2cea45c9b452 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonD.lean#L133-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonD.lean#L133-L139

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

theorem P2M_ReciprocityTheory_ChartRestriction_L1_divBy_C_mul__2cea45c9b452 {x c : K} (hc : ‖c‖ ≤ ‖x‖) {f : PowerSeries K} (hf : IntegralPS f) :
    DivBy x (C c * f) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«L1».«divBy_C_mul'» := P2M_ReciprocityTheory_ChartRestriction_L1_divBy_C_mul__2cea45c9b452
