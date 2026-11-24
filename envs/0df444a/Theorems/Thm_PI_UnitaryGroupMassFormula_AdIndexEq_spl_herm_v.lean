-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_spl_herm_v
-- name    : PI.UnitaryGroupMassFormula.AdIndexEq.spl_herm_v
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T14:10:18.544643+00:00
-- url     : https://prove2.me/theorems/8fe39ffe-d4aa-4054-b9de-4830cbd32f71
-- title:
--   Ad Index Eq: spl herm v
-- statement:
--   The Ad Index Eq construction uses the spl herm v property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/LocSplitChiOf.lean#L29-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/LocSplitChiOf.lean#L29-L36

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_SplitIso
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_SplitGL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_LocSplitChiOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.MainNotions.S

theorem PI.UnitaryGroupMassFormula.AdIndexEq.spl_herm_v (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) :
    Formalism.UG.cT (sigV I v) (I.J.map (inclV I v)) = I.J.map (inclV I v) := by sorry
