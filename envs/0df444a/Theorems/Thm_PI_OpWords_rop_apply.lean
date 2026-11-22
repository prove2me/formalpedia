-- Prove2me | Theorems.Thm_PI_OpWords_rop_apply
-- name    : PI.OpWords.rop_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:13:52.49716+00:00
-- url     : https://prove2.me/theorems/b7c89970-bcc4-47ba-b190-46fbc0548d94
-- title:
--   Op Words: rop apply
-- statement:
--   The Op Words construction uses the rop apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/VanishExp.lean#L14-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/VanishExp.lean#L14-L15

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_VanishExp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open PI PI.OpWords
variable {K : Type} [Field K] [CharZero K] {k : ℕ}

theorem PI.OpWords.rop_apply (a b : Fin k) (f : Pol K k) :
    Rop K k a b f = X (Sum.inl a) * pderiv (Sum.inl b) f - X (Sum.inr b) * pderiv (Sum.inr a) f := by sorry
