-- Prove2me | Theorems.Thm_PI_BeDiagZp_IdentW_l_ex_apply
-- name    : PI.BeDiagZp.IdentW.l_ex_apply
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:25:03.122645+00:00
-- url     : https://prove2.me/theorems/6e274cae-7a68-5ad5-a51f-fff5dc56403b
-- title:
--   Ident W: l ex apply
-- statement:
--   The Ident W construction uses the l ex apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/CoeffOneLNeZero.lean#L54-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/CoeffOneLNeZero.lean#L54-L60

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

theorem PI.BeDiagZp.IdentW.l_ex_apply {σ : Type} {l ex : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
    (h : PowerSeries.subst ex l = PowerSeries.X) (y : MvPowerSeries σ ℂ_[p])
    (hy : MvPowerSeries.constantCoeff y = 0) :
    PowerSeries.subst (PowerSeries.subst y ex) l = y := by sorry
