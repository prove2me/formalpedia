-- Prove2me | Theorems.Thm_PI_BeDiagZp_SubstW_deg_eq
-- name    : PI.BeDiagZp.SubstW.deg_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:24:52.710722+00:00
-- url     : https://prove2.me/theorems/3742c8bb-740d-586e-afea-7fa574cce1b5
-- title:
--   Subst W: deg eq
-- statement:
--   The Subst W construction uses the deg eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/PowerSeriesDiagonalLinear.lean#L94-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/PowerSeriesDiagonalLinear.lean#L94-L96

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

theorem PI.BeDiagZp.SubstW.deg_eq {σ : Type*} (α : σ →₀ ℕ) : (α.sum fun _ k => k) = α.degree := by sorry
