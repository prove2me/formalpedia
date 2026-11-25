-- Prove2me | Theorems.Thm_PI_KerDetFinW_natCast_mem_int
-- name    : PI.KerDetFinW.natCast_mem_int
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:32:24.880369+00:00
-- url     : https://prove2.me/theorems/306ec8cd-a189-43c1-8470-dfe37d4a163f
-- title:
--   Ker Det Fin W: nat Cast mem int
-- statement:
--   The Ker Det Fin W construction uses the nat Cast mem int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DeterminantKernelFiniteness/ExistsNatMulMemFracFam.lean#L12-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DeterminantKernelFiniteness/ExistsNatMulMemFracFam.lean#L12-L14

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

theorem PI.KerDetFinW.natCast_mem_int {K : Type} [Field K] [NumberField K] (N : ℕ) :
    (N : K) ∈ (algebraMap (𝓞 K) K).range := by sorry
