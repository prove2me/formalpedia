-- Prove2me | Theorems.Thm_PI_WfSubstProof_coeff_map_mem
-- name    : PI.WfSubstProof.coeff_map_mem
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:59:03.580979+00:00
-- url     : https://prove2.me/theorems/dab5bf6d-3db2-5c51-97f6-7c98c115529e
-- title:
--   Wf Subst Proof: coeff map mem
-- statement:
--   The Wf Subst Proof construction uses the coeff map mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WittSubstitution/CoeffMapMem.lean#L18-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WittSubstitution/CoeffMapMem.lean#L18-L21

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WfSubst
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_InvNatMemWf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittSubstitution_CoeffMapMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WfSubstProof

theorem PI.WfSubstProof.coeff_map_mem {A : Type} [CommRing A] (S : Subring A) {σ : Type} (g : MvPowerSeries σ S)
    (e : σ →₀ ℕ) : MvPowerSeries.coeff e (MvPowerSeries.map S.subtype g) ∈ S := by sorry
