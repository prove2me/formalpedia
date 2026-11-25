-- Prove2me | Theorems.Thm_PI_VolStabW_isOpen_unitHerm
-- name    : PI.VolStabW.isOpen_unitHerm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:14:43.266875+00:00
-- url     : https://prove2.me/theorems/a578d3a6-e768-41e1-8b94-6e4bde40b5e6
-- title:
--   Vol Stab W: is Open unit Herm
-- statement:
--   The Vol Stab W construction uses the is Open unit Herm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/TensTop.lean#L249-L251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/TensTop.lean#L249-L251

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
  [LocallyCompactSpace R] [T2Space R]

theorem PI.VolStabW.isOpen_unitHerm (h : IsOpen {r : R | IsUnit r}) (σ : E →ₐ[F] E) (n : ℕ) :
    IsOpen {S : HermR R σ n | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} := by sorry
