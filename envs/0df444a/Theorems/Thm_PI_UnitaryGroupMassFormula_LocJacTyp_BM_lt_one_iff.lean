-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_BM_lt_one_iff
-- name    : PI.UnitaryGroupMassFormula.LocJacTyp.BM.lt_one_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:40:15.926649+00:00
-- url     : https://prove2.me/theorems/0b3750d5-16bf-4897-b59e-2a2f3079724d
-- title:
--   BM: lt one iff
-- statement:
--   The BM construction uses the lt one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/BoxMulA.lean#L91-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/BoxMulA.lean#L91-L104

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

theorem PI.UnitaryGroupMassFormula.LocJacTyp.BM.lt_one_iff (ϖ : Fv F v) (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (y : Fv F v) :
    Valued.v y < 1 ↔ Valued.v (ϖ⁻¹ * y) ≤ 1 := by sorry
