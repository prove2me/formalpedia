-- Prove2me | Theorems.Thm_PIW_AdelClassFin_DictRing_tmul_mem
-- name    : PIW.AdelClassFin.DictRing.tmul_mem
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T13:29:46.82767+00:00
-- url     : https://prove2.me/theorems/19cab8de-df8e-4b9a-b8fd-b17cebd6e2df
-- title:
--   Dict Ring: tmul mem
-- statement:
--   The Dict Ring construction uses the tmul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/DictRing.lean#L174-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/DictRing.lean#L174-L179

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
variable {E : Type} [Field E] [NumberField E] [Algebra F E]

theorem PIW.AdelClassFin.DictRing.tmul_mem {x : E} (hx : x ∈ Formalism.UG.intOE E) {y : Af F} (hy : y ∈ Formalism.UG.intAd F) :
    x ⊗ₜ[F] y ∈ IntAf F E := by sorry
