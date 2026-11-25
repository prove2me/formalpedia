-- Prove2me | Theorems.Thm_PI_AprimeInfT_secondCountable_tens
-- name    : PI.AprimeInfT.secondCountable_tens
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:09:47.511022+00:00
-- url     : https://prove2.me/theorems/51e25f22-543e-5952-941c-8dc8a052e57e
-- title:
--   Aprime Inf T: second Countable tens
-- statement:
--   The Aprime Inf T construction uses the second Countable tens property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/T2SpaceTensorProductFiniteExtension.lean#L32-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/T2SpaceTensorProductFiniteExtension.lean#L32-L34

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

theorem PI.AprimeInfT.secondCountable_tens [SecondCountableTopology R] : SecondCountableTopology (R ⊗[F] E) := by sorry
