-- Prove2me | Theorems.Thm_PI_EF_PK_side_split
-- name    : PI.EF.PK.side_split
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:28:17.604387+00:00
-- url     : https://prove2.me/theorems/31f82819-4915-455a-a2dd-3f3efbb0ae29
-- title:
--   PK: side split
-- statement:
--   The PK construction uses the side split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/PerronKernelA.lean#L141-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/PerronKernelA.lean#L141-L149

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_RectInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronKernelA
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

theorem PI.EF.PK.side_split (l : ℝ) (γ : ℝ → ℂ) (hγ : Continuous γ) (h0 : ∀ t, γ t ≠ 0) (p q : ℝ) :
    ∫ t in p..q, ker l (γ t) = (∫ t in p..q, gl l (γ t)) + ∫ t in p..q, 1 / (γ t - 0) := by sorry
