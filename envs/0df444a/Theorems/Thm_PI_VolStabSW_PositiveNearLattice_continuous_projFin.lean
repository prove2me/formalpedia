-- Prove2me | Theorems.Thm_PI_VolStabSW_PositiveNearLattice_continuous_projFin
-- name    : PI.VolStabSW.PositiveNearLattice.continuous_projFin
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T00:58:33.371996+00:00
-- url     : https://prove2.me/theorems/1f3a98db-4c77-4abf-8ab7-af99ab20be25
-- title:
--   Positive Near Lattice: continuous proj Fin
-- statement:
--   The Positive Near Lattice construction uses the continuous proj Fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/PosNear.lean#L162-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/PosNear.lean#L162-L166

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
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
variable [FiniteDimensional F E] {d : ℕ} (b : Module.Basis (Fin d) F E)
include b

theorem PI.VolStabSW.PositiveNearLattice.continuous_projFin {M a : ℕ} :
    Continuous (projFin (F := F) (E := E) (M := M) (n := a)) := by sorry
