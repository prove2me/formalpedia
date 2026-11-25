-- Prove2me | Theorems.Thm_PIW_AdelClassFin_DictRing_int_mem
-- name    : PIW.AdelClassFin.DictRing.int_mem
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:54:10.442787+00:00
-- url     : https://prove2.me/theorems/79f1a038-5c83-529c-9562-615521a2201f
-- title:
--   Dict Ring: int mem
-- statement:
--   The Dict Ring construction uses the int mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/DictRing.lean#L34-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/DictRing.lean#L34-L42

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

theorem PIW.AdelClassFin.DictRing.int_mem (r : 𝓞 F) (v : HeightOneSpectrum (𝓞 F)) :
    algebraMap (𝓞 F) (v.adicCompletion F) r ∈ v.adicCompletionIntegers F := by sorry
