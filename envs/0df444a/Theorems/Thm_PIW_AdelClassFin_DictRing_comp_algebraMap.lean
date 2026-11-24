-- Prove2me | Theorems.Thm_PIW_AdelClassFin_DictRing_comp_algebraMap
-- name    : PIW.AdelClassFin.DictRing.comp_algebraMap
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T13:30:07.16526+00:00
-- url     : https://prove2.me/theorems/26a71460-996d-49fc-98a6-65cb19ed08b9
-- title:
--   Dict Ring: comp algebra Map
-- statement:
--   The Dict Ring construction uses the comp algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/DictRing.lean#L30-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/DictRing.lean#L30-L32

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictPlan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StrongApproximation_DedekindLFunctions
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelClassFin
open Formalism.MainNotions.S PI.AdelClassFin NumberField IsDedekindDomain
open scoped TensorProduct Matrix
open PIW.AdelClassFin.DictRing
variable {F : Type} [Field F] [NumberField F]

theorem PIW.AdelClassFin.DictRing.comp_algebraMap (r : 𝓞 F) (v : HeightOneSpectrum (𝓞 F)) :
    (algebraMap (𝓞 F) (Af F) r) v = algebraMap (𝓞 F) (v.adicCompletion F) r := by sorry
