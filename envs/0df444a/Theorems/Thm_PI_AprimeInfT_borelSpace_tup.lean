-- Prove2me | Theorems.Thm_PI_AprimeInfT_borelSpace_tup
-- name    : PI.AprimeInfT.borelSpace_tup
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:10:06.814329+00:00
-- url     : https://prove2.me/theorems/f16241d3-af04-5bfc-95d6-2d4f8c86b5b6
-- title:
--   Aprime Inf T: borel Space tup
-- statement:
--   The Aprime Inf T construction uses the borel Space tup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/T2SpaceTensorProductFiniteExtension.lean#L119-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/T2SpaceTensorProductFiniteExtension.lean#L119-L123

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

theorem PI.AprimeInfT.borelSpace_tup [SecondCountableTopology R] (a : ℕ) :
    BorelSpace (Fin a → Fin M → R ⊗[F] E) := by sorry
