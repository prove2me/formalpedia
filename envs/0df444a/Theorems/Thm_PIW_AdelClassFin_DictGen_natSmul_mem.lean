-- Prove2me | Theorems.Thm_PIW_AdelClassFin_DictGen_natSmul_mem
-- name    : PIW.AdelClassFin.DictGen.natSmul_mem
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T13:28:35.329498+00:00
-- url     : https://prove2.me/theorems/9ed9a4dc-ab93-4a30-8f91-22f8967bccbd
-- title:
--   Dict Gen: nat Smul mem
-- statement:
--   The Dict Gen construction uses the nat Smul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/DictGen.lean#L20-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/DictGen.lean#L20-L27

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

theorem PIW.AdelClassFin.DictGen.natSmul_mem (k : ℕ) {w : Fin I.n → I.E ⊗[I.F] Af I.F} (hw : w ∈ I.Lf) :
    (k : I.E ⊗[I.F] Af I.F) • w ∈ I.Lf := by sorry
