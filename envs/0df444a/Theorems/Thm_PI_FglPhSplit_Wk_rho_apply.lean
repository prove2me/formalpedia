-- Prove2me | Theorems.Thm_PI_FglPhSplit_Wk_rho_apply
-- name    : PI.FglPhSplit.Wk.rho_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:01.952667+00:00
-- url     : https://prove2.me/theorems/07d3e292-86e7-4a33-aa32-994da0779074
-- title:
--   Wk: rho apply
-- statement:
--   The Wk construction uses the rho apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupSplitting/ExpCongruenceExtendsToSum.lean#L89-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupSplitting/ExpCongruenceExtendsToSum.lean#L89-L92

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_AddPreservesExpCongruence
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_OrthogonalSplitPolarizationVanishes
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_ExpCongruenceExtendsToSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FglPhSplit PI.FglPhSplit.Wk
open PI.FglPhSplit
variable {K : Type} [Field K]
variable {ι ι' : Type} [Fintype ι]

theorem PI.FglPhSplit.Wk.rho_apply (F : MvPowerSeries (ι ⊕ ι) K) :
    (rho (ι' := ι') F) = MvPowerSeries.subst
      (fun j : ι ⊕ ι => (MvPowerSeries.X (Sum.inl j) : MvPowerSeries ((ι ⊕ ι) ⊕ ι') K)) F := by sorry
