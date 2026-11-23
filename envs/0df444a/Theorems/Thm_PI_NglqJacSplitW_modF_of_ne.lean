-- Prove2me | Theorems.Thm_PI_NglqJacSplitW_modF_of_ne
-- name    : PI.NglqJacSplitW.modF_of_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:34:50.240863+00:00
-- url     : https://prove2.me/theorems/935d0c2c-11f5-40d4-9ac4-10a9e7688d29
-- title:
--   Nglq Jac Split W: mod F of ne
-- statement:
--   The Nglq Jac Split W construction uses the mod F of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JacobianTransvectionSplitting/FactorOneOfDiscrete.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JacobianTransvectionSplitting/FactorOneOfDiscrete.lean#L17-L19

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeNGLQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianTransvectionSplitting_DiscreteHaar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianTransvectionSplitting_FactorOneOfDiscrete
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ENNReal NNReal
open PI PI.NglqJacSplitW
variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F]
  [LocallyCompactSpace F]

theorem PI.NglqJacSplitW.modF_of_ne {a : F} (h : a ≠ 0) :
    modF F a = ((distribHaarChar F (Units.mk0 a h) : ℝ≥0) : ℝ≥0∞) := by sorry
