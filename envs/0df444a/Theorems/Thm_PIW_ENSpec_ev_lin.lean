-- Prove2me | Theorems.Thm_PIW_ENSpec_ev_lin
-- name    : PIW.ENSpec.ev_lin
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:49:27.845288+00:00
-- url     : https://prove2.me/theorems/8e7d56a2-278b-4336-a74d-ab4428fd26a6
-- title:
--   ENSpec: ev lin
-- statement:
--   The ENSpec construction uses the ev lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/EagonNorthcottComplex/Assemble.lean#L14-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/EagonNorthcottComplex/Assemble.lean#L14-L15

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottComplex_StSpecOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottComplex_Assemble
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open PIW PIW.ENSpec
open PI.EagonNorthcott MvPolynomial RingTheory.Sequence
variable {R : Type u} [CommRing R] {D : ℕ} (x : Fin D → R)

theorem PIW.ENSpec.ev_lin (c : Fin D → ℤ) : eval x (lin (X : Fin D → MvPolynomial (Fin D) R) c) = lin x c := by sorry
