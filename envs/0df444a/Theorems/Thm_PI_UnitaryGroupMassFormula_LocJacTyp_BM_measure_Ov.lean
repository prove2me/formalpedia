-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_BM_measure_Ov
-- name    : PI.UnitaryGroupMassFormula.LocJacTyp.BM.measure_Ov
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:40:12.24451+00:00
-- url     : https://prove2.me/theorems/262f9a8e-bfbb-4827-8a61-6d74e771aeef
-- title:
--   BM: measure Ov
-- statement:
--   The BM construction uses the measure Ov property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/BoxMulA.lean#L117-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/BoxMulA.lean#L117-L175

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocJacTyp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianTransvectionSplitting_DiscreteHaar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_AdeleLC
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_GlobalClassField_LocPowB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_BoxMulA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LocJacTyp PI.UnitaryGroupMassFormula.LocJacTyp.BM
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacTyp
open scoped ENNReal NNReal Pointwise
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem PI.UnitaryGroupMassFormula.LocJacTyp.BM.measure_Ov [MeasurableSpace (Fv F v)] [BorelSpace (Fv F v)] (μ : Measure (Fv F v))
    [μ.IsAddLeftInvariant] (ϖ : Fv F v) (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) :
    (Ideal.absNorm v.asIdeal : ℝ≥0∞) * μ (Mv v ϖ) = μ (Ov v) := by sorry
