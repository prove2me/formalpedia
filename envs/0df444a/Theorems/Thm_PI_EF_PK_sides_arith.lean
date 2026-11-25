-- Prove2me | Theorems.Thm_PI_EF_PK_sides_arith
-- name    : PI.EF.PK.sides_arith
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:28:28.7443+00:00
-- url     : https://prove2.me/theorems/48d81616-005a-54d4-836c-e8fe19e0c7df
-- title:
--   PK: sides arith
-- statement:
--   The PK construction uses the sides arith property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/ContinuousInvSqrt.lean#L169-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/ContinuousInvSqrt.lean#L169-L203

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronTruncOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_ContinuousInvSqrt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.EF PI.EF.PK
open Complex MeasureTheory intervalIntegral Real

theorem PI.EF.PK.sides_arith {C1 C2 u T T' c l1 l2 as large₂ lNu uc : ℝ} (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hT0 : 0 < T)
    (hu0 : 0 < u) (hTu : T ≤ u) (hTT' : T ≤ T') (hc1 : 1 < c) (hc3 : c ≤ 3) (huc0 : 0 ≤ uc)
    (huc : uc ≤ 3 * u)
    (hLg0 : 0 ≤ large₂) (hl1 : l1 ≤ large₂) (hl1' : 0 ≤ l1) (hl2 : l2 ≤ 2 * large₂) (has : as ≤ 2 * large₂)
    (has0 : 0 ≤ as) (hlNu : 0 ≤ lNu) :
    C1 * l1 ^ 2 * (uc / T') * (c - -1 / 2) + C1 * l1 ^ 2 * (uc / T') * (c - -1 / 2) +
      C2 * l2 * (2 * as) ≤ (21 * C1 + 8 * C2) * (u * large₂ ^ 2 / T + lNu) := by sorry
