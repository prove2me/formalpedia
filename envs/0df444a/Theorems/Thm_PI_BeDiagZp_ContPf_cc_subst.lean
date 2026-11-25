-- Prove2me | Theorems.Thm_PI_BeDiagZp_ContPf_cc_subst
-- name    : PI.BeDiagZp.ContPf.cc_subst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:40:41.284872+00:00
-- url     : https://prove2.me/theorems/35271d1c-fa8d-4a27-a5c0-7fbe10e1eead
-- title:
--   Cont Pf: cc subst
-- statement:
--   The Cont Pf construction uses the cc subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/ConstantCoeffSubstEqZero.lean#L61-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/ConstantCoeffSubstEqZero.lean#L61-L68

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

theorem PI.BeDiagZp.ContPf.cc_subst {σ : Type} (F : PowerSeries ℂ_[p]) {G : ℂ_[p] → MvPowerSeries σ ℂ_[p]}
    (h0 : ∀ c, MvPowerSeries.constantCoeff (G c) = 0) (hG : CC G) :
    CC fun c => PowerSeries.subst (G c) F := by sorry
