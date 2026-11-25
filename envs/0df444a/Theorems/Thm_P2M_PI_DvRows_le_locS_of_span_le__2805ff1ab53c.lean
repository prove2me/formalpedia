-- Prove2me | Theorems.Thm_P2M_PI_DvRows_le_locS_of_span_le__2805ff1ab53c
-- name    : P2M_PI_DvRows_le_locS_of_span_le__2805ff1ab53c
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:57:10.299704+00:00
-- url     : https://prove2.me/theorems/4d969137-3c18-4404-8e16-227ea9f9b442
-- title:
--   P2 M PI Dv Rows le loc S of span le  2805ff1ab53c: P2 M PI Dv Rows le loc S of span le  2805ff1ab53c
-- statement:
--   The P2 M PI Dv Rows le loc S of span le  2805ff1ab53c construction uses the P2 M PI Dv Rows le loc S of span le  2805ff1ab53c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/LatticeFinitelyGenerated.lean#L339-L361
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/LatticeFinitelyGenerated.lean#L339-L361

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

theorem P2M_PI_DvRows_le_locS_of_span_le__2805ff1ab53c (X Y : Submodule R V)
    (h : Submodule.span K (X : Set V) ≤ Submodule.span K (Y : Set V)) :
    X ≤ locS (nonZeroDivisors R) Y := by sorry

alias «PI».«DvRows».«le_locS_of_span_le'» := P2M_PI_DvRows_le_locS_of_span_le__2805ff1ab53c
