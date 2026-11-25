-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_Cj_transvection_transpose
-- name    : PI.VolSemiDirect.W.Cj.transvection_transpose
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:37:31.926886+00:00
-- url     : https://prove2.me/theorems/cd6d9952-7581-5d81-aff5-aa520eb4d935
-- title:
--   Cj: transvection transpose
-- statement:
--   The Cj construction uses the transvection transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/NnrealEqOneOfMulSelf.lean#L52-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/NnrealEqOneOfMulSelf.lean#L52-L56

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_MapPhiOfModM
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_NnrealEqOneOfMulSelf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W PI.VolSemiDirect.W.Cj
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Measure
open scoped NNReal
variable {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [LocallyCompactSpace A] [SecondCountableTopology A] [T2Space A] [MeasurableSpace A]
  [BorelSpace A] {k : ℕ}

theorem PI.VolSemiDirect.W.Cj.transvection_transpose (i j : Fin k) (c : A) :
    (Matrix.transvection i j c).transpose = Matrix.transvection j i c := by sorry
