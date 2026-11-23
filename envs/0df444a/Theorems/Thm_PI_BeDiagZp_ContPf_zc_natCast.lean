-- Prove2me | Theorems.Thm_PI_BeDiagZp_ContPf_zc_natCast
-- name    : PI.BeDiagZp.ContPf.zc_natCast
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:41:23.819046+00:00
-- url     : https://prove2.me/theorems/0a310c59-3756-4461-a1df-81d50e07f275
-- title:
--   Cont Pf: zc nat Cast
-- statement:
--   The Cont Pf construction uses the zc nat Cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/ConstantCoeffSubstEqZero.lean#L86-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/ConstantCoeffSubstEqZero.lean#L86-L87

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

theorem PI.BeDiagZp.ContPf.zc_natCast (n : ℕ) : zc (n : ℤ_[p]) = (n : ℂ_[p]) := by sorry
