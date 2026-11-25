-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_Cj_modM_transv
-- name    : PI.VolSemiDirect.W.Cj.modM_transv
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:37:20.880091+00:00
-- url     : https://prove2.me/theorems/d0d97f84-2c6f-412a-a707-0f30679da57f
-- title:
--   Cj: mod M transv
-- statement:
--   The Cj construction uses the mod M transv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/NnrealEqOneOfMulSelf.lean#L42-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/NnrealEqOneOfMulSelf.lean#L42-L50

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

theorem PI.VolSemiDirect.W.Cj.modM_transv (hT : TransvHaar) (X : GL (Fin k) A) (i j : Fin k) (hij : i ≠ j) (c : A)
    (hX : (X : Matrix (Fin k) (Fin k) A) = Matrix.transvection i j c) : modM X = 1 := by sorry
