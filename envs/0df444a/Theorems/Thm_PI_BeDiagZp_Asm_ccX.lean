-- Prove2me | Theorems.Thm_PI_BeDiagZp_Asm_ccX
-- name    : PI.BeDiagZp.Asm.ccX
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:40:17.377985+00:00
-- url     : https://prove2.me/theorems/d735ed7b-959f-4463-be67-3544b2379fde
-- title:
--   Asm: cc X
-- statement:
--   The Asm construction uses the cc X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/SimeqCongr.lean#L34-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/SimeqCongr.lean#L34-L35

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_SubstOps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_SimeqCongr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.BeDiagZp
open PI.BeDiagZp.Asm
variable {p : ℕ} [Fact p.Prime]

theorem PI.BeDiagZp.Asm.ccX {σ : Type} (i : σ) : MvPowerSeries.constantCoeff (Xv i : MvPowerSeries σ ℂ_[p]) = 0 := by sorry
