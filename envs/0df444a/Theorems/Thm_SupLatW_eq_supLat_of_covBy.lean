-- Prove2me | Theorems.Thm_SupLatW_eq_supLat_of_covBy
-- name    : SupLatW.eq_supLat_of_covBy
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:10:47.06126+00:00
-- url     : https://prove2.me/theorems/019a62fb-1231-41f8-a40e-593b281001b2
-- title:
--   Sup Lat W: eq sup Lat of cov By
-- statement:
--   The Sup Lat W construction uses the eq sup Lat of cov By property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeSupremumLine/EqSupLatOfCovBy.lean#L168-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeSupremumLine/EqSupLatOfCovBy.lean#L168-L220

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

theorem SupLatW.eq_supLat_of_covBy {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] {ϖ : R} (hϖ : Irreducible ϖ) {r : ℕ}
    (M : Submodule R (Fin r → K)) (hM : stdLat R K r ⋖ M) :
    ∃ x : Fin r → R, (∃ i, ¬ ϖ ∣ x i) ∧ M = supLat R K ϖ x := by sorry
