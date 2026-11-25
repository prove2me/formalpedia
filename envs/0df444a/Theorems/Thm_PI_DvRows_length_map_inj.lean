-- Prove2me | Theorems.Thm_PI_DvRows_length_map_inj
-- name    : PI.DvRows.length_map_inj
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:29:07.996406+00:00
-- url     : https://prove2.me/theorems/0b554541-39a4-4d5b-b069-9083a0691ed3
-- title:
--   Dv Rows: length map inj
-- statement:
--   The Dv Rows construction uses the length map inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/LatticeFinitelyGenerated.lean#L285-L303
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/LatticeFinitelyGenerated.lean#L285-L303

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

theorem PI.DvRows.length_map_inj (f : W →ₗ[R] W') (hf : Function.Injective f) (X Z : Submodule R W) :
    Module.length R (↥(Z.map f) ⧸ (X.map f).comap (Z.map f).subtype) =
      Module.length R (↥Z ⧸ X.comap Z.subtype) := by sorry
