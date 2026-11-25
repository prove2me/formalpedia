-- Prove2me | Theorems.Thm_PI_VolStabSW_smul_ratTup_cont
-- name    : PI.VolStabSW.smul_ratTup_cont
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:46:12.192609+00:00
-- url     : https://prove2.me/theorems/172ea77f-4de8-4ebc-b437-b139d1dce551
-- title:
--   Vol Stab SW: smul rat Tup cont
-- statement:
--   The Vol Stab SW construction uses the smul rat Tup cont property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/ExStabTop.lean#L52-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/ExStabTop.lean#L52-L61

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_ExStabSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_ExStabTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct ENNReal

theorem PI.VolStabSW.smul_ratTup_cont (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
    [FiniteDimensional F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) {a : ℕ}
    (X0 : Fin a → Fin M → E) :
    Continuous (fun g : HA (AF F) σ J => g • ratTup (F := F) (AF F) X0) := by sorry
