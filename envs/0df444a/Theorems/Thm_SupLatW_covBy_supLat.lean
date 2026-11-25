-- Prove2me | Theorems.Thm_SupLatW_covBy_supLat
-- name    : SupLatW.covBy_supLat
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:10:47.966315+00:00
-- url     : https://prove2.me/theorems/80e9cbae-f7fe-410a-96e2-33f6445259ab
-- title:
--   Sup Lat W: cov By sup Lat
-- statement:
--   The Sup Lat W construction uses the cov By sup Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeSupremumLine/EqSupLatOfCovBy.lean#L128-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeSupremumLine/EqSupLatOfCovBy.lean#L128-L166

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

theorem SupLatW.covBy_supLat {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] {ϖ : R} (hϖ : Irreducible ϖ) {r : ℕ}
    (x : Fin r → R) (hx : ∃ i, ¬ ϖ ∣ x i) : stdLat R K r ⋖ supLat R K ϖ x := by sorry
