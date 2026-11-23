-- Prove2me | Theorems.Thm_PI_VolStabSW_PositiveNearLattice_continuous_map_tens
-- name    : PI.VolStabSW.PositiveNearLattice.continuous_map_tens
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T00:58:31.695156+00:00
-- url     : https://prove2.me/theorems/56334ff6-8b4d-4edb-ba87-965af43cff0d
-- title:
--   Positive Near Lattice: continuous map tens
-- statement:
--   The Positive Near Lattice construction uses the continuous map tens property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/PosNear.lean#L50-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/PosNear.lean#L50-L61

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibInfEx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_ReciprocityTheory_GeneralLinearIntegers_AlgebraMapIntMemOint
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_PosNear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open PI.VolStabSW.PositiveNearLattice
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)
variable [FiniteDimensional F E]
include b

theorem PI.VolStabSW.PositiveNearLattice.continuous_map_tens {R S : Type} [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] [CommRing S] [Algebra F S] [TopologicalSpace S] [IsTopologicalRing S]
    (f : R →ₐ[F] S) (hf : Continuous f) :
    Continuous (Algebra.TensorProduct.map f (AlgHom.id F E)) := by sorry
