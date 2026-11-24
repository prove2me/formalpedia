-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_BM_dhc_unit
-- name    : PI.UnitaryGroupMassFormula.LocJacTyp.BM.dhc_unit
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:26:57.35593+00:00
-- url     : https://prove2.me/theorems/8893b29f-b35e-412f-ae94-610c16fd5d2b
-- title:
--   BM: dhc unit
-- statement:
--   The BM construction uses the dhc unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/BoxMulA.lean#L208-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/BoxMulA.lean#L208-L226

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

theorem PI.UnitaryGroupMassFormula.LocJacTyp.BM.dhc_unit (u : Fv F v) (hu : Valued.v u = 1) (hu0 : u ≠ 0) :
    distribHaarChar (Fv F v) (Units.mk0 u hu0) = 1 := by sorry
