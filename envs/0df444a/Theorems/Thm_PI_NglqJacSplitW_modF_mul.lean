-- Prove2me | Theorems.Thm_PI_NglqJacSplitW_modF_mul
-- name    : PI.NglqJacSplitW.modF_mul
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:34:57.032061+00:00
-- url     : https://prove2.me/theorems/7d2f341a-a858-469e-a3f0-5c6078df5232
-- title:
--   Nglq Jac Split W: mod F mul
-- statement:
--   The Nglq Jac Split W construction uses the mod F mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JacobianTransvectionSplitting/FactorOneOfDiscrete.lean#L21-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JacobianTransvectionSplitting/FactorOneOfDiscrete.lean#L21-L25

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

theorem PI.NglqJacSplitW.modF_mul {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) : modF F (a * b) = modF F a * modF F b := by sorry
