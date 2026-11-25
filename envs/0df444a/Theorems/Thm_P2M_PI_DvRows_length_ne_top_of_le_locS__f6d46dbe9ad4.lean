-- Prove2me | Theorems.Thm_P2M_PI_DvRows_length_ne_top_of_le_locS__f6d46dbe9ad4
-- name    : P2M_PI_DvRows_length_ne_top_of_le_locS__f6d46dbe9ad4
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:55:39.686803+00:00
-- url     : https://prove2.me/theorems/3d7fc187-1684-58ec-af2d-9269929dae0a
-- title:
--   P2 M PI Dv Rows length ne top of le loc S  f6d46dbe9ad4: P2 M PI Dv Rows length ne top of le loc S  f6d46dbe9ad4
-- statement:
--   The P2 M PI Dv Rows length ne top of le loc S  f6d46dbe9ad4 construction uses the P2 M PI Dv Rows length ne top of le loc S  f6d46dbe9ad4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/LatticeFinitelyGenerated.lean#L363-L367
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/LatticeFinitelyGenerated.lean#L363-L367

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Pieces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndexDeterminant_NegLogValuation
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_LatticeFinitelyGenerated
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.DvRows
open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv
open Formalism.HermitianLatticesTheory
variable {R K V : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem P2M_PI_DvRows_length_ne_top_of_le_locS__f6d46dbe9ad4 [IsNoetherianRing R] [Ring.KrullDimLE 1 R] (p : Ideal R)
    [p.IsPrime] (X Y : Submodule R V) (hX : X.FG) (hXY : X ≤ locS (nonZeroDivisors R) Y) :
    Module.length R (↥(localization₂ p X) ⧸ (localization₂ p Y).comap (localization₂ p X).subtype) ≠ ⊤ := by sorry

alias «PI».«DvRows».«length_ne_top_of_le_locS'» := P2M_PI_DvRows_length_ne_top_of_le_locS__f6d46dbe9ad4
