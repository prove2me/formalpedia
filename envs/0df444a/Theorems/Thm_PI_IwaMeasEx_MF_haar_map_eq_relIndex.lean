-- Prove2me | Theorems.Thm_PI_IwaMeasEx_MF_haar_map_eq_relIndex
-- name    : PI.IwaMeasEx.MF.haar_map_eq_relIndex
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:45:52.188929+00:00
-- url     : https://prove2.me/theorems/55443c1c-6a82-4471-a06b-6134669f207a
-- title:
--   MF: haar map eq rel Index
-- statement:
--   The MF construction uses the haar map eq rel Index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IwasawaMeasureExistence/MeasureEqRelIndexMul.lean#L88-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IwasawaMeasureExistence/MeasureEqRelIndexMul.lean#L88-L159

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IwasawaMeasureExistence_MeasureEqRelIndexMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.IwaMeasEx PI.IwaMeasEx.MF
open MeasureTheory Measure Set
open scoped ENNReal NNReal
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [MeasurableSpace G] [BorelSpace G]

theorem PI.IwaMeasEx.MF.haar_map_eq_relIndex (φ : G ≃ₜ* G) (U : Subgroup G) (hUo : IsOpen (U : Set G))
    (hUc : IsCompact (U : Set G))
    (h1 : (U ⊓ U.comap φ.toMulEquiv.toMonoidHom).relIndex U ≠ 0)
    (h2 : (U ⊓ U.comap φ.toMulEquiv.toMonoidHom).relIndex (U.comap φ.toMulEquiv.toMonoidHom) ≠ 0) :
    (haar : Measure G).map φ = ENNReal.ofReal
      (((U ⊓ U.comap φ.toMulEquiv.toMonoidHom).relIndex (U.comap φ.toMulEquiv.toMonoidHom) : ℝ) /
        ((U ⊓ U.comap φ.toMulEquiv.toMonoidHom).relIndex U : ℝ)) • (haar : Measure G) := by sorry
