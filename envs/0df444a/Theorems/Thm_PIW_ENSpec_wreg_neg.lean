-- Prove2me | Theorems.Thm_PIW_ENSpec_wreg_neg
-- name    : PIW.ENSpec.wreg_neg
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:47:06.706019+00:00
-- url     : https://prove2.me/theorems/fc05cf01-5250-4301-a669-890cf6abae90
-- title:
--   ENSpec: wreg neg
-- statement:
--   The ENSpec construction uses the wreg neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/EagonNorthcottComplex/WregOfSubsingleton.lean#L41-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/EagonNorthcottComplex/WregOfSubsingleton.lean#L41-L58

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottComplex_StSpecOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottComplex_WregOfSubsingleton
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open PIW PIW.ENSpec
open MvPolynomial RingTheory.Sequence
open scoped Pointwise
variable {S : Type u} [CommRing S]

theorem PIW.ENSpec.wreg_neg {M : Type v} [AddCommGroup M] [Module S M] (rs : List S) :
    IsWeaklyRegular M (rs.map Neg.neg) ↔ IsWeaklyRegular M rs := by sorry
