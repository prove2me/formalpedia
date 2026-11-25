-- Prove2me | Theorems.Thm_PI_VolStabW_RestrProdA_hasProd_ofReal_of_complex
-- name    : PI.VolStabW.RestrProdA.hasProd_ofReal_of_complex
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:38:47.096371+00:00
-- url     : https://prove2.me/theorems/2dd12cda-6d16-48a5-9a1b-9668e7af9fe8
-- title:
--   Restr Prod A: has Prod of Real of complex
-- statement:
--   The Restr Prod A construction uses the has Prod of Real of complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/RestrProdA.lean#L27-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/RestrProdA.lean#L27-L34

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProdSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_PosNear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProdA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.RestrProdA
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

theorem PI.VolStabW.RestrProdA.hasProd_ofReal_of_complex {β : Type} {f : β → ℝ} (hf : ∀ b, 0 ≤ f b) {q : ℂ}
    (h : HasProd (fun b => (f b : ℂ)) q) :
    HasProd (fun b => ENNReal.ofReal (f b)) (ENNReal.ofReal q.re) := by sorry
