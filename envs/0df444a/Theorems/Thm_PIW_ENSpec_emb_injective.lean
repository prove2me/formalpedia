-- Prove2me | Theorems.Thm_PIW_ENSpec_emb_injective
-- name    : PIW.ENSpec.emb_injective
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:48:00.764806+00:00
-- url     : https://prove2.me/theorems/f5111edd-0e2f-4673-adcf-b63ebe2df662
-- title:
--   ENSpec: emb injective
-- statement:
--   The ENSpec construction uses the emb injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/EagonNorthcottComplex/WregOfSubsingleton.lean#L116-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/EagonNorthcottComplex/WregOfSubsingleton.lean#L116-L121

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
variable {R : Type u} [CommRing R] {D : ℕ}
local notation "𝔛" => Ideal.span (Set.range (MvPolynomial.X : Fin D → MvPolynomial (Fin D) R))

theorem PIW.ENSpec.emb_injective (a : ℕ) : Function.Injective (emb (R := R) (D := D) a) := by sorry
