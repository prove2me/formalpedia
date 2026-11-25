-- Prove2me | Theorems.Thm_PI_CntNotIntW_val_one_of_not_mem
-- name    : PI.CntNotIntW.val_one_of_not_mem
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:26:09.168804+00:00
-- url     : https://prove2.me/theorems/0fe72591-367e-438f-ba6e-de0520257680
-- title:
--   Cnt Not Int W: val one of not mem
-- statement:
--   The Cnt Not Int W construction uses the val one of not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CountNonIntegrality/ValOneOfNotMem.lean#L61-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CountNonIntegrality/ValOneOfNotMem.lean#L61-L63

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountNonIntegrality_ValOneOfNotMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.CntNotIntW
open NumberField IsDedekindDomain ValuativeRel
variable {E : Type} [Field E] [NumberField E] {K : Type} [Field K] [ValuativeRel K]

theorem PI.CntNotIntW.val_one_of_not_mem (σ : E →+* K) (l : ℕ) (hl0 : l ≠ 0) (hl : valuation K (l : K) < 1) (s : 𝓞 E)
    (hs : s ∉ (vPrime σ l hl0 hl).asIdeal) : valuation K (σ (s : E)) = 1 := by sorry
