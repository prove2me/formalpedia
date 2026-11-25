-- Prove2me | Theorems.Thm_PIW_ENSpec_wreg_ses
-- name    : PIW.ENSpec.wreg_ses
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:47:27.10631+00:00
-- url     : https://prove2.me/theorems/0d755ec6-85a4-47fc-bbd9-a69e567ecee9
-- title:
--   ENSpec: wreg ses
-- statement:
--   The ENSpec construction uses the wreg ses property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/EagonNorthcottComplex/WregOfSubsingleton.lean#L23-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/EagonNorthcottComplex/WregOfSubsingleton.lean#L23-L39

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

theorem PIW.ENSpec.wreg_ses (rs : List S) : ∀ {M' M M'' : Type v} [AddCommGroup M'] [Module S M'] [AddCommGroup M]
    [Module S M] [AddCommGroup M''] [Module S M''] (f : M' →ₗ[S] M) (g : M →ₗ[S] M''),
    Function.Injective f → Function.Exact f g → Function.Surjective g →
    IsWeaklyRegular M' rs → IsWeaklyRegular M'' rs → IsWeaklyRegular M rs := by sorry
