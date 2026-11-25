-- Prove2me | Theorems.Thm_PI_LocCartanPair_splPlane_entry
-- name    : PI.LocCartanPair.splPlane_entry
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:34:25.206044+00:00
-- url     : https://prove2.me/theorems/f3584962-e2b9-50d2-af61-629942e1b07f
-- title:
--   Loc Cartan Pair: spl Plane entry
-- statement:
--   The Loc Cartan Pair construction uses the spl Plane entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/SplPlane.lean#L11-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/SplPlane.lean#L11-L14

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_SplPlane
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.LocCartanPair
variable {R : Type} [CommRing R] [StarRing R]

theorem PI.LocCartanPair.splPlane_entry {ι m n : Type} [Fintype ι] (A : Matrix ι ι R) (M : Matrix ι m R)
    (N : Matrix ι n R) (r : m) (s : n) :
    (Mᴴ * A * N) r s = star (fun i => M i r) ⬝ᵥ (A *ᵥ fun i => N i s) := by sorry
