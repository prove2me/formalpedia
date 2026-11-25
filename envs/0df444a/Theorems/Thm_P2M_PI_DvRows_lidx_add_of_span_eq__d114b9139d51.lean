-- Prove2me | Theorems.Thm_P2M_PI_DvRows_lidx_add_of_span_eq__d114b9139d51
-- name    : P2M_PI_DvRows_lidx_add_of_span_eq__d114b9139d51
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:11:27.353051+00:00
-- url     : https://prove2.me/theorems/0a2ec7f9-c175-4b7f-95c8-0caa24002529
-- title:
--   P2 M PI Dv Rows lidx add of span eq  d114b9139d51: P2 M PI Dv Rows lidx add of span eq  d114b9139d51
-- statement:
--   The P2 M PI Dv Rows lidx add of span eq  d114b9139d51 construction uses the P2 M PI Dv Rows lidx add of span eq  d114b9139d51 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/LatticeFinitelyGenerated.lean#L369-L390
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/LatticeFinitelyGenerated.lean#L369-L390

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

theorem P2M_PI_DvRows_lidx_add_of_span_eq__d114b9139d51 [IsNoetherianRing R] [Ring.KrullDimLE 1 R] (p : Ideal R) [p.IsPrime]
    (A B C : Submodule R V) (hA : A.FG) (hB : B.FG) (hC : C.FG)
    (hAB : Submodule.span K (A : Set V) = Submodule.span K (B : Set V))
    (hBC : Submodule.span K (B : Set V) = Submodule.span K (C : Set V)) :
    lidx p A C = lidx p A B + lidx p B C := by sorry

alias «PI».«DvRows».«lidx_add_of_span_eq'» := P2M_PI_DvRows_lidx_add_of_span_eq__d114b9139d51
