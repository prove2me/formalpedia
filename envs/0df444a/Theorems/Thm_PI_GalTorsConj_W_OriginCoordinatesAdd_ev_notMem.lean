-- Prove2me | Theorems.Thm_PI_GalTorsConj_W_OriginCoordinatesAdd_ev_notMem
-- name    : PI.GalTorsConj.W.OriginCoordinatesAdd.ev_notMem
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:30:39.968091+00:00
-- url     : https://prove2.me/theorems/dc91ca35-fe7c-59d2-98e8-e9cc131034b3
-- title:
--   Origin Coordinates Add: ev not Mem
-- statement:
--   The Origin Coordinates Add construction uses the ev not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GaloisTorsionConjugacy/AddLaw.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GaloisTorsionConjugacy/AddLaw.lean#L19-L21

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_WpBridge
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_AddLaw
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.GalTorsConj PI.GalTorsConj.W
open Formalism.L2.Th1.F
open Filter Topology
open PI.GalTorsConj.W.OriginCoordinatesAdd

theorem PI.GalTorsConj.W.OriginCoordinatesAdd.ev_notMem (L : PeriodPair) {f : ℂ → ℂ} {z : ℂ} (hf : ContinuousAt f z)
    (h : f z ∉ L.lattice) : ∀ᶠ z' in 𝓝 z, f z' ∉ L.lattice := by sorry
