-- Prove2me | Theorems.Thm_PI_AprimeInfT_secondCountable_HA
-- name    : PI.AprimeInfT.secondCountable_HA
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:10:38.300891+00:00
-- url     : https://prove2.me/theorems/1621abf9-46af-40e3-a51f-6e5f96556868
-- title:
--   Aprime Inf T: second Countable HA
-- statement:
--   The Aprime Inf T construction uses the second Countable HA property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/T2SpaceTensorProductFiniteExtension.lean#L96-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/T2SpaceTensorProductFiniteExtension.lean#L96-L107

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_T2SpaceTensorProductFiniteExtension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.AprimeInfT
open scoped TensorProduct
open NumberField MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
variable [LocallyCompactSpace R] [T2Space R]
variable {M : ℕ}

theorem PI.AprimeInfT.secondCountable_HA [SecondCountableTopology R] (σ : E →ₐ[F] E)
    (J : Matrix (Fin M) (Fin M) E) : SecondCountableTopology (HA R σ J) := by sorry
