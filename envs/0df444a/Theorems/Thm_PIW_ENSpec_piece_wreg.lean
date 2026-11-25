-- Prove2me | Theorems.Thm_PIW_ENSpec_piece_wreg
-- name    : PIW.ENSpec.piece_wreg
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:47:15.380007+00:00
-- url     : https://prove2.me/theorems/b9122576-92f4-4228-b0ad-2eb8a157a79b
-- title:
--   ENSpec: piece wreg
-- statement:
--   The ENSpec construction uses the piece wreg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/EagonNorthcottComplex/WregOfSubsingleton.lean#L151-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/EagonNorthcottComplex/WregOfSubsingleton.lean#L151-L160

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

theorem PIW.ENSpec.piece_wreg (a : ℕ) (x : Fin D → R) (hx : IsWeaklyRegular R (List.ofFn x)) :
    IsWeaklyRegular (LinearMap.ker (gmap (R := R) (D := D) a)) (tl x) := by sorry
