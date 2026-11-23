-- Prove2me | Theorems.Thm_P2M_PI_DvRows_mem_locP__7b0c6c9a7105
-- name    : P2M_PI_DvRows_mem_locP__7b0c6c9a7105
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:11:06.403179+00:00
-- url     : https://prove2.me/theorems/3526ae8e-4dfc-4baa-9899-0552b2d96e59
-- title:
--   P2 M PI Dv Rows mem loc P  7b0c6c9a7105: P2 M PI Dv Rows mem loc P  7b0c6c9a7105
-- statement:
--   The P2 M PI Dv Rows mem loc P  7b0c6c9a7105 construction uses the P2 M PI Dv Rows mem loc P  7b0c6c9a7105 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/LatticeFinitelyGenerated.lean#L267-L268
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/LatticeFinitelyGenerated.lean#L267-L268

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
variable {R : Type*} [CommRing R] {W W' : Type*} [AddCommGroup W] [Module R W]
  [AddCommGroup W'] [Module R W']

theorem P2M_PI_DvRows_mem_locP__7b0c6c9a7105 (p : Ideal R) [p.IsPrime] {A : Submodule R W} {x : W} :
    x ∈ localization₂ p A ↔ ∃ s ∈ p.primeCompl, s • x ∈ A := by sorry

alias «PI».«DvRows».«mem_locP'» := P2M_PI_DvRows_mem_locP__7b0c6c9a7105
