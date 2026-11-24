-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_spl_sig_sig
-- name    : PI.UnitaryGroupMassFormula.AdIndexEq.spl_sig_sig
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T14:10:16.699464+00:00
-- url     : https://prove2.me/theorems/3b6e490c-fb11-4e24-82e4-81dd81836eac
-- title:
--   Ad Index Eq: spl sig sig
-- statement:
--   The Ad Index Eq construction uses the spl sig sig property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/LocSplitChiOf.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/LocSplitChiOf.lean#L17-L19

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

theorem PI.UnitaryGroupMassFormula.AdIndexEq.spl_sig_sig (I : AutInst) (a : I.E) : I.cm.sig (I.cm.sig a) = a := by sorry
