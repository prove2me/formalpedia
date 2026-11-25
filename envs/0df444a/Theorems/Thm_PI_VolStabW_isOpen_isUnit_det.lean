-- Prove2me | Theorems.Thm_PI_VolStabW_isOpen_isUnit_det
-- name    : PI.VolStabW.isOpen_isUnit_det
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:51:46.178325+00:00
-- url     : https://prove2.me/theorems/7c01ac75-2c6c-5475-9dd2-5f8f767b1296
-- title:
--   Vol Stab W: is Open is Unit det
-- statement:
--   The Vol Stab W construction uses the is Open is Unit det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/TensTop.lean#L61-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/TensTop.lean#L61-L65

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_VolFromSW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TensTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]

theorem PI.VolStabW.isOpen_isUnit_det (h : IsOpen {r : R | IsUnit r}) (n : ℕ) :
    IsOpen {S : Matrix (Fin n) (Fin n) (R ⊗[F] E) | IsUnit S.det} := by sorry
