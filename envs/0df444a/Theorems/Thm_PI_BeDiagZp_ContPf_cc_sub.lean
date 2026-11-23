-- Prove2me | Theorems.Thm_PI_BeDiagZp_ContPf_cc_sub
-- name    : PI.BeDiagZp.ContPf.cc_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:40:40.270547+00:00
-- url     : https://prove2.me/theorems/b33991d8-84de-40b2-bb21-1c46d0d2d77d
-- title:
--   Cont Pf: cc sub
-- statement:
--   The Cont Pf construction uses the cc sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/ConstantCoeffSubstEqZero.lean#L28-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/ConstantCoeffSubstEqZero.lean#L28-L30

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

theorem PI.BeDiagZp.ContPf.cc_sub {σ : Type} {F G : ℂ_[p] → MvPowerSeries σ ℂ_[p]} (hF : CC F) (hG : CC G) :
    CC fun c => F c - G c := by sorry
