-- Prove2me | Theorems.Thm_PIW_AdelClassFin_DictLat_Lf_le
-- name    : PIW.AdelClassFin.DictLat.Lf_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T13:29:23.442352+00:00
-- url     : https://prove2.me/theorems/53c4537d-3545-4cae-aa77-a58bb2e50bb5
-- title:
--   Dict Lat: Lf le
-- statement:
--   The Dict Lat construction uses the Lf le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/DictLat.lean#L104-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/DictLat.lean#L104-L109

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictPlan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictLat
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

theorem PIW.AdelClassFin.DictLat.Lf_le (I : AutInst) (p : Submodule (IntAf I.F I.E) (Fin I.n → I.E ⊗[I.F] Af I.F))
    (h : ∀ l ∈ I.L, iv I l ∈ p) : I.Lf ≤ p := by sorry
