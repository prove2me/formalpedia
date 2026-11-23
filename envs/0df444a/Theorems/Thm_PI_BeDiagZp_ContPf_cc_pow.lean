-- Prove2me | Theorems.Thm_PI_BeDiagZp_ContPf_cc_pow
-- name    : PI.BeDiagZp.ContPf.cc_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:38:33.611135+00:00
-- url     : https://prove2.me/theorems/9f3c7b8c-739c-4cb3-ab77-155ccf7ef9a3
-- title:
--   Cont Pf: cc pow
-- statement:
--   The Cont Pf construction uses the cc pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/ConstantCoeffSubstEqZero.lean#L38-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/ConstantCoeffSubstEqZero.lean#L38-L42

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

theorem PI.BeDiagZp.ContPf.cc_pow {σ : Type} {F : ℂ_[p] → MvPowerSeries σ ℂ_[p]} (hF : CC F) (k : ℕ) :
    CC fun c => F c ^ k := by sorry
