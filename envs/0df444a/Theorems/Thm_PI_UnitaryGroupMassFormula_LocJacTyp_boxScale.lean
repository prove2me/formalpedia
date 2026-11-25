-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_boxScale
-- name    : PI.UnitaryGroupMassFormula.LocJacTyp.boxScale
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:57:34.240536+00:00
-- url     : https://prove2.me/theorems/a2425b21-2d91-4cec-86b2-cc38b978e967
-- title:
--   Loc Jac Typ: box Scale
-- statement:
--   The Loc Jac Typ construction uses the box Scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/KitScale.lean#L25-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/KitScale.lean#L25-L32

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocJacTyp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_BoxMulAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_KitAbs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_BoxMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_KitScale
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LocJacTyp
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacTyp
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

theorem PI.UnitaryGroupMassFormula.LocJacTyp.boxScale {ι : Type} [Fintype ι] (hfin : Module.finrank F E = 2)
    (μ : Measure (ι → Fv F v ⊗[F] E)) [μ.IsAddHaarMeasure] (x : ι → Fv F v) (hx : ∀ i, x i ≠ 0) :
    (μ (Set.univ.pi fun i => {c | sc (E := E) v (x i) * c ∈ OEv (E := E) v})).toReal =
      (μ (Obox (E := E) v ι)).toReal * ∏ i, (absV v (x i) ^ 2)⁻¹ := by sorry
