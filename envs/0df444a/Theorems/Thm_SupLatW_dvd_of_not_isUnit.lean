-- Prove2me | Theorems.Thm_SupLatW_dvd_of_not_isUnit
-- name    : SupLatW.dvd_of_not_isUnit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:23:24.228902+00:00
-- url     : https://prove2.me/theorems/a769f8da-d605-4cac-837c-86d09eadf065
-- title:
--   Sup Lat W: dvd of not is Unit
-- statement:
--   The Sup Lat W construction uses the dvd of not is Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeSupremumLine/EqSupLatOfCovBy.lean#L60-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeSupremumLine/EqSupLatOfCovBy.lean#L60-L66

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

theorem SupLatW.dvd_of_not_isUnit {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {ϖ : R} (hϖ : Irreducible ϖ) {s : R} (hs : ¬ IsUnit s) : ϖ ∣ s := by sorry
