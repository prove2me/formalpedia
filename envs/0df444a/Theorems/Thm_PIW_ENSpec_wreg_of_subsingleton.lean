-- Prove2me | Theorems.Thm_PIW_ENSpec_wreg_of_subsingleton
-- name    : PIW.ENSpec.wreg_of_subsingleton
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:47:07.857814+00:00
-- url     : https://prove2.me/theorems/ee308a1f-d2c1-5c9d-aa8f-69a88116c0e2
-- title:
--   ENSpec: wreg of subsingleton
-- statement:
--   The ENSpec construction uses the wreg of subsingleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/EagonNorthcottComplex/WregOfSubsingleton.lean#L15-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/EagonNorthcottComplex/WregOfSubsingleton.lean#L15-L21

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

theorem PIW.ENSpec.wreg_of_subsingleton {M : Type v} [AddCommGroup M] [Module S M] [Subsingleton M] (rs : List S) :
    IsWeaklyRegular M rs := by sorry
