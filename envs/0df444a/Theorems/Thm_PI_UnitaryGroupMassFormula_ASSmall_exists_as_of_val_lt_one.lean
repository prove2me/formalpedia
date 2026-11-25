-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_ASSmall_exists_as_of_val_lt_one
-- name    : PI.UnitaryGroupMassFormula.ASSmall.exists_as_of_val_lt_one
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:38:03.141455+00:00
-- url     : https://prove2.me/theorems/6205d316-b16e-4e42-96ee-db70466f79eb
-- title:
--   ASSmall: exists as of val lt one
-- statement:
--   The ASSmall construction uses the exists as of val lt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SmallArtinSchreier/ExistsAsOfValLtOne.lean#L37-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SmallArtinSchreier/ExistsAsOfValLtOne.lean#L37-L40

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ArtSch
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SmallArtinSchreier_CoordPowEqZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SmallArtinSchreier_ExistsAsOfValLtOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ASSmall
open scoped NNReal
variable {K : Type*} [Field K] {v : Valuation K ℝ≥0} {O : Type*} [CommRing O] [Algebra O K]
  (hv : v.Integers O) {p : ℕ} [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
include hv

theorem PI.UnitaryGroupMassFormula.ASSmall.exists_as_of_val_lt_one (hp : 0 < v (p : K)) (e : PreTilt O p)
    (he : PreTilt.val K v O hv p e < 1) : ∃ w : PreTilt O p, w ^ p - w = e := by sorry
