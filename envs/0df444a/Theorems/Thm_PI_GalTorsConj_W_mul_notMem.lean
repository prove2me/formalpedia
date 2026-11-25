-- Prove2me | Theorems.Thm_PI_GalTorsConj_W_mul_notMem
-- name    : PI.GalTorsConj.W.mul_notMem
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:31:15.179067+00:00
-- url     : https://prove2.me/theorems/127bf548-d527-4a21-af34-3db8bc658719
-- title:
--   W: mul not Mem
-- statement:
--   The W construction uses the mul not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GaloisTorsionConjugacy/MulMain.lean#L106-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GaloisTorsionConjugacy/MulMain.lean#L106-L117

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_MulDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_AddLaw
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_AddDbl
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_WpOnto
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_MulMain
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

theorem PI.GalTorsConj.W.mul_notMem {L : PeriodPair} {c z : ℂ} {S : Finset ℂ} (hS : IsKerReps L c S)
    (hz : z ∉ L.lattice) (hzP : ∀ P ∈ S, z + P ∉ L.lattice) :
    c * z ∉ L.lattice := by sorry
