-- Prove2me | Theorems.Thm_PI_KerDetFinW_exists_nat_mul_mem_int_fam
-- name    : PI.KerDetFinW.exists_nat_mul_mem_int_fam
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:32:25.295065+00:00
-- url     : https://prove2.me/theorems/329d5283-1a71-4da1-bc90-7eff72a6fe91
-- title:
--   Ker Det Fin W: exists nat mul mem int fam
-- statement:
--   The Ker Det Fin W construction uses the exists nat mul mem int fam property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DeterminantKernelFiniteness/ExistsNatMulMemFracFam.lean#L34-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DeterminantKernelFiniteness/ExistsNatMulMemFracFam.lean#L34-L40

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerIso
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantKernelFiniteness_ExistsNatMulMemFracFam
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
open PI PI.KerDetFinW
open PI.KerIso

theorem PI.KerDetFinW.exists_nat_mul_mem_int_fam {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
    (f : ι → K) : ∃ N : ℕ, 0 < N ∧ ∀ i, (N : K) * f i ∈ (algebraMap (𝓞 K) K).range := by sorry
