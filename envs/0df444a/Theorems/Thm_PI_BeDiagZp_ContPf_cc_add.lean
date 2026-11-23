-- Prove2me | Theorems.Thm_PI_BeDiagZp_ContPf_cc_add
-- name    : PI.BeDiagZp.ContPf.cc_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:40:59.584452+00:00
-- url     : https://prove2.me/theorems/4f07c297-0395-4d47-8072-b1aa45893fda
-- title:
--   Cont Pf: cc add
-- statement:
--   The Cont Pf construction uses the cc add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/ConstantCoeffSubstEqZero.lean#L24-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/ConstantCoeffSubstEqZero.lean#L24-L26

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_SubstOps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_ConstantCoeffSubstEqZero
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
open PI PI.BeDiagZp PI.BeDiagZp.ContPf
variable {p : ℕ} [Fact p.Prime]

theorem PI.BeDiagZp.ContPf.cc_add {σ : Type} {F G : ℂ_[p] → MvPowerSeries σ ℂ_[p]} (hF : CC F) (hG : CC G) :
    CC fun c => F c + G c := by sorry
