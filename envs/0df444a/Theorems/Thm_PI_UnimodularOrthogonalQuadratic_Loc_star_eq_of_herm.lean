-- Prove2me | Theorems.Thm_PI_UnimodularOrthogonalQuadratic_Loc_star_eq_of_herm
-- name    : PI.UnimodularOrthogonalQuadratic.Loc.star_eq_of_herm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:42:49.552612+00:00
-- url     : https://prove2.me/theorems/2c3342f7-9efe-4a04-b4f6-b0e0c0b1fbfe
-- title:
--   Loc: star eq of herm
-- statement:
--   The Loc construction uses the star eq of herm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularOrthogonal/LocalOrthogonalMatrixOddPrime.lean#L28-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularOrthogonal/LocalOrthogonalMatrixOddPrime.lean#L28-L30

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularOrthogonal_MatOrthoLocal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularOrthogonal_LocalOrthogonalMatrixOddPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnimodularOrthogonalQuadratic PI.UnimodularOrthogonalQuadratic.Loc
open Matrix
variable {S : Type} [CommRing S] [StarRing S]

theorem PI.UnimodularOrthogonalQuadratic.Loc.star_eq_of_herm {n : ℕ} {H : Matrix (Fin n) (Fin n) S} (hH : Hᴴ = H) (k l : Fin n) :
    star (H k l) = H l k := by sorry
