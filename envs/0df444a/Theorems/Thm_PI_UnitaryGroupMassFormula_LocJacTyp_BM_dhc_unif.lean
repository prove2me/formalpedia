-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_BM_dhc_unif
-- name    : PI.UnitaryGroupMassFormula.LocJacTyp.BM.dhc_unif
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:26:57.938964+00:00
-- url     : https://prove2.me/theorems/a963bf5e-313f-4202-bbad-c6c8f936a5f0
-- title:
--   BM: dhc unif
-- statement:
--   The BM construction uses the dhc unif property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/BoxMulA.lean#L181-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/BoxMulA.lean#L181-L206

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
variable [LocallyCompactSpace (Fv F v)]

theorem PI.UnitaryGroupMassFormula.LocJacTyp.BM.dhc_unif (ϖ : Fv F v) (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (hϖ0 : ϖ ≠ 0) :
    distribHaarChar (Fv F v) (Units.mk0 ϖ hϖ0) = ((Ideal.absNorm v.asIdeal : ℝ≥0))⁻¹ := by sorry
