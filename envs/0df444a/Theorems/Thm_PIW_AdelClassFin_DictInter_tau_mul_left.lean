-- Prove2me | Theorems.Thm_PIW_AdelClassFin_DictInter_tau_mul_left
-- name    : PIW.AdelClassFin.DictInter.tau_mul_left
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:48:43.257426+00:00
-- url     : https://prove2.me/theorems/9b6b82ae-053b-4aa6-9867-4fe4a7eae622
-- title:
--   Dict Inter: tau mul left
-- statement:
--   The Dict Inter construction uses the tau mul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/DictInter.lean#L26-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/DictInter.lean#L26-L32

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictPlan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictInter
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
open scoped TensorProduct Matrix nonZeroDivisors
open PIW.AdelClassFin.DictInter
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem PIW.AdelClassFin.DictInter.tau_mul_left (w a : E) (r : E ⊗[F] Af F) :
    tau w ((a ⊗ₜ[F] (1 : Af F)) * r) = tau (w * a) r := by sorry
