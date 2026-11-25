-- Prove2me | Theorems.Thm_PIW_AdelClassFin_DictGen_natCast_cancel
-- name    : PIW.AdelClassFin.DictGen.natCast_cancel
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:50:30.489814+00:00
-- url     : https://prove2.me/theorems/422ad011-c63f-500b-9792-6e42e7eb7c92
-- title:
--   Dict Gen: nat Cast cancel
-- statement:
--   The Dict Gen construction uses the nat Cast cancel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/DictGen.lean#L36-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/DictGen.lean#L36-L45

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictPlan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictGen
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
open Formalism.MainNotions.S PI.AdelClassFin NumberField
open scoped TensorProduct Matrix
open PIW.AdelClassFin.DictGen
variable (I : AutInst)

theorem PIW.AdelClassFin.DictGen.natCast_cancel (N : ℕ) (hN : 0 < N) {a b : Fin I.n → I.E ⊗[I.F] Af I.F}
    (h : (N : I.E ⊗[I.F] Af I.F) • a = (N : I.E ⊗[I.F] Af I.F) • b) : a = b := by sorry
