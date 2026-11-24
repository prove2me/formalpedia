-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_spl_det_v
-- name    : PI.UnitaryGroupMassFormula.AdIndexEq.spl_det_v
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T14:11:22.215945+00:00
-- url     : https://prove2.me/theorems/e59c4456-a1b8-4fe2-ab0f-0abecd60f6a2
-- title:
--   Ad Index Eq: spl det v
-- statement:
--   The Ad Index Eq construction uses the spl det v property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/LocSplitChiOf.lean#L38-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/LocSplitChiOf.lean#L38-L42

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

theorem PI.UnitaryGroupMassFormula.AdIndexEq.spl_det_v (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) : IsUnit (I.J.map (inclV I v)).det := by sorry
