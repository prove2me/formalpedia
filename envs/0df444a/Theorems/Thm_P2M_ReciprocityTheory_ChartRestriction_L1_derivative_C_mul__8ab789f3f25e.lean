-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_L1_derivative_C_mul__8ab789f3f25e
-- name    : P2M_ReciprocityTheory_ChartRestriction_L1_derivative_C_mul__8ab789f3f25e
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:16:44.233545+00:00
-- url     : https://prove2.me/theorems/b8afa23c-edfc-422c-bc75-136f67b0cf0d
-- title:
--   P2 M Reciprocity Theory Chart Restriction L1 derivative C mul  8ab789f3f25e: P2 M Reciprocity Theory Chart Restriction L1 derivative C mul  8ab789f3f25e
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction L1 derivative C mul  8ab789f3f25e construction uses the P2 M Reciprocity Theory Chart Restriction L1 derivative C mul  8ab789f3f25e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonD.lean#L141-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonD.lean#L141-L143

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

theorem P2M_ReciprocityTheory_ChartRestriction_L1_derivative_C_mul__8ab789f3f25e (c : K) (f : PowerSeries K) :
    derivative K (C c * f) = C c * derivative K f := by sorry

alias «ReciprocityTheory».«ChartRestriction».«L1».«derivative_C_mul'» := P2M_ReciprocityTheory_ChartRestriction_L1_derivative_C_mul__8ab789f3f25e
