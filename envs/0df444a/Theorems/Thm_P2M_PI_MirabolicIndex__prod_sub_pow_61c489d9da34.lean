-- Prove2me | Theorems.Thm_P2M_PI_MirabolicIndex__prod_sub_pow_61c489d9da34
-- name    : P2M_PI_MirabolicIndex__prod_sub_pow_61c489d9da34
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:56:58.148702+00:00
-- url     : https://prove2.me/theorems/ebd3b615-8dae-4bbd-adc0-8624528225d4
-- title:
--   P2 M PI Mirabolic Index  prod sub pow 61c489d9da34: P2 M PI Mirabolic Index  prod sub pow 61c489d9da34
-- statement:
--   The P2 M PI Mirabolic Index  prod sub pow 61c489d9da34 construction uses the P2 M PI Mirabolic Index  prod sub pow 61c489d9da34 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirabolicIndex/RowMulOfMirab.lean#L8-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirabolicIndex/RowMulOfMirab.lean#L8-L27

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_MirabIndex
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirabolicIndex_RowMulOfMirab
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.MirabolicIndex₂
open Finset Matrix PI.MirabIndex

theorem P2M_PI_MirabolicIndex__prod_sub_pow_61c489d9da34 (q n : ℕ) :
    ∏ i : Fin n, (q ^ (n + 1) - q ^ ((i : ℕ) + 1)) =
      q ^ ((n + 1) * n / 2) * ∏ i ∈ Finset.Ico 1 (n + 1), (q ^ i - 1) := by sorry

alias «PI».«MirabolicIndex₂».«prod_sub_pow» := P2M_PI_MirabolicIndex__prod_sub_pow_61c489d9da34
