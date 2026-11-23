-- Prove2me | Theorems.Thm_SupLatW_mem_stdLat_iff
-- name    : SupLatW.mem_stdLat_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:50:18.216564+00:00
-- url     : https://prove2.me/theorems/f508cf75-eea3-475d-8a7d-00411ae31daa
-- title:
--   Sup Lat W: mem std Lat iff
-- statement:
--   The Sup Lat W construction uses the mem std Lat iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeSupremumLine/EqSupLatOfCovBy.lean#L8-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeSupremumLine/EqSupLatOfCovBy.lean#L8-L36

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

theorem SupLatW.mem_stdLat_iff {R K : Type} [CommRing R] [Field K] [Algebra R K] {r : ℕ}
    (v : Fin r → K) : v ∈ stdLat R K r ↔ ∃ x : Fin r → R, v = vecK R K x := by sorry
