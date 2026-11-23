-- Prove2me | Theorems.Thm_PI_BeDiagZp_IdentW_constantCoeff_l
-- name    : PI.BeDiagZp.IdentW.constantCoeff_l
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:38:50.75301+00:00
-- url     : https://prove2.me/theorems/d45accab-cb0d-43cf-89b5-156a343736bf
-- title:
--   Ident W: constant Coeff l
-- statement:
--   The Ident W construction uses the constant Coeff l property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/CoeffOneLNeZero.lean#L11-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/CoeffOneLNeZero.lean#L11-L18

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

theorem PI.BeDiagZp.IdentW.constantCoeff_l {l ex : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
    (h : PowerSeries.subst ex l = PowerSeries.X) : PowerSeries.constantCoeff l = 0 := by sorry
