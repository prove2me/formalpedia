-- Prove2me | Theorems.Thm_PI_BeDiagZp_ContPf_zc_continuous
-- name    : PI.BeDiagZp.ContPf.zc_continuous
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:40:59.511553+00:00
-- url     : https://prove2.me/theorems/00c53d4b-0513-4417-8b39-f677852c26b4
-- title:
--   Cont Pf: zc continuous
-- statement:
--   The Cont Pf construction uses the zc continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/ConstantCoeffSubstEqZero.lean#L82-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/ConstantCoeffSubstEqZero.lean#L82-L84

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

theorem PI.BeDiagZp.ContPf.zc_continuous : Continuous (zc : ℤ_[p] → ℂ_[p]) := by sorry
