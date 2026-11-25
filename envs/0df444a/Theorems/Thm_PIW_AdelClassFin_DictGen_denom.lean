-- Prove2me | Theorems.Thm_PIW_AdelClassFin_DictGen_denom
-- name    : PIW.AdelClassFin.DictGen.denom
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:53:41.301795+00:00
-- url     : https://prove2.me/theorems/26950cfc-9a83-4787-9807-a7fbbb05c005
-- title:
--   Dict Gen: denom
-- statement:
--   The Dict Gen construction uses the denom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/DictGen.lean#L109-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/DictGen.lean#L109-L123

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

theorem PIW.AdelClassFin.DictGen.denom (hD : LDenom) (M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
    ∃ N : ℕ, 0 < N ∧ ∀ y ∈ I.Lf, (N : I.E ⊗[I.F] Af I.F) • (M *ᵥ y) ∈ I.Lf := by sorry
