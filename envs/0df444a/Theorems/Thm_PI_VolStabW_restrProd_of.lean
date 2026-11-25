-- Prove2me | Theorems.Thm_PI_VolStabW_restrProd_of
-- name    : PI.VolStabW.restrProd_of
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:54:27.912051+00:00
-- url     : https://prove2.me/theorems/6d4c0ae9-928f-5c63-a7c6-6a024f277518
-- title:
--   Vol Stab W: restr Prod of
-- statement:
--   The Vol Stab W construction uses the restr Prod of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/RestrProdSt.lean#L84-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/RestrProdSt.lean#L84-L173

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_VolStabFromSWW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProdSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

theorem PI.VolStabW.restrProd_of (hA : RPAbs) (hF : RPFib) (hG : RPGlue) (hGr : RPGram) (hTl : RPTail)
    (hL : LatCofin) : RestrProd := by sorry
