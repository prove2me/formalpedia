-- Prove2me | Theorems.Thm_SupLatW_inv_smul_mem_iff
-- name    : SupLatW.inv_smul_mem_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:51:15.360113+00:00
-- url     : https://prove2.me/theorems/14ec6c68-e8be-41d9-8f32-690774827b15
-- title:
--   Sup Lat W: inv smul mem iff
-- statement:
--   The Sup Lat W construction uses the inv smul mem iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeSupremumLine/EqSupLatOfCovBy.lean#L42-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeSupremumLine/EqSupLatOfCovBy.lean#L42-L58

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GlobalRankLatticeProofs_UnitTraceSumBounds_FGTorsionFreeGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSupremumLine_EqSupLatOfCovBy
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open SupLatW
open Formalism.MainNotions.Ext.CutC

theorem SupLatW.inv_smul_mem_iff {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {ϖ : R} (hϖ : Irreducible ϖ) {r : ℕ} (x : Fin r → R) :
    (algebraMap R K ϖ)⁻¹ • vecK R K x ∈ stdLat R K r ↔ ∀ i, ϖ ∣ x i := by sorry
