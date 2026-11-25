-- Prove2me | Theorems.Thm_PI_BeDiagZp_IdentW_subst_left_inv
-- name    : PI.BeDiagZp.IdentW.subst_left_inv
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:24:43.168845+00:00
-- url     : https://prove2.me/theorems/576ec528-2d2a-488b-84c9-d2fabd98d56e
-- title:
--   Ident W: subst left inv
-- statement:
--   The Ident W construction uses the subst left inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/CoeffOneLNeZero.lean#L38-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/CoeffOneLNeZero.lean#L38-L48

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_SubstOps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_CoeffOneLNeZero
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
open PI PI.BeDiagZp PI.BeDiagZp.IdentW
variable {p : ℕ} [Fact p.Prime]

theorem PI.BeDiagZp.IdentW.subst_left_inv {K : Type*} [Field K] {l ex : PowerSeries K} (hl0 : PowerSeries.constantCoeff l = 0)
    (hu : IsUnit (PowerSeries.coeff 1 l)) (hex0 : PowerSeries.constantCoeff ex = 0)
    (h : PowerSeries.subst ex l = PowerSeries.X) : PowerSeries.subst l ex = PowerSeries.X := by sorry
