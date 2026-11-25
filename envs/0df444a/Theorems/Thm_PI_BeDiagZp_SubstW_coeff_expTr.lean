-- Prove2me | Theorems.Thm_PI_BeDiagZp_SubstW_coeff_expTr
-- name    : PI.BeDiagZp.SubstW.coeff_expTr
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:24:35.928443+00:00
-- url     : https://prove2.me/theorems/0f24e010-e455-5fe0-96ec-aaf014ece130
-- title:
--   Subst W: coeff exp Tr
-- statement:
--   The Subst W construction uses the coeff exp Tr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/PowerSeriesDiagonalLinear.lean#L122-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/PowerSeriesDiagonalLinear.lean#L122-L127

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_SubstOps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_PowerSeriesDiagonalLinear
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
open PI PI.BeDiagZp PI.BeDiagZp.SubstW
variable {p : ℕ} [Fact p.Prime]

theorem PI.BeDiagZp.SubstW.coeff_expTr {σ : Type*} (F : MvPowerSeries σ ℂ_[p]) (N : ℕ) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d (expTr F N) =
      ∑ n ∈ Finset.range N, MvPowerSeries.coeff d (F ^ n) / (n.factorial : ℂ_[p]) := by sorry
