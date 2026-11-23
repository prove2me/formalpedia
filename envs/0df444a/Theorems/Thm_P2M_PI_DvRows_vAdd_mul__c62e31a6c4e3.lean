-- Prove2me | Theorems.Thm_P2M_PI_DvRows_vAdd_mul__c62e31a6c4e3
-- name    : P2M_PI_DvRows_vAdd_mul__c62e31a6c4e3
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:11:57.7648+00:00
-- url     : https://prove2.me/theorems/db61d1ff-4c09-42f7-bd70-4891e1004246
-- title:
--   P2 M PI Dv Rows v Add mul  c62e31a6c4e3: P2 M PI Dv Rows v Add mul  c62e31a6c4e3
-- statement:
--   The P2 M PI Dv Rows v Add mul  c62e31a6c4e3 construction uses the P2 M PI Dv Rows v Add mul  c62e31a6c4e3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/LatticeFinitelyGenerated.lean#L400-L404
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/LatticeFinitelyGenerated.lean#L400-L404

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
variable {K : Type} [Field K] [NumberField K]

theorem P2M_PI_DvRows_vAdd_mul__c62e31a6c4e3 (w : HeightOneSpectrum (𝓞 K)) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    vAdd w (x * y) = vAdd w x + vAdd w y := by sorry

alias «PI».«DvRows».«vAdd_mul'» := P2M_PI_DvRows_vAdd_mul__c62e31a6c4e3
