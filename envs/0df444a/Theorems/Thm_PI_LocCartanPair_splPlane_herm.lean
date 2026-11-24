-- Prove2me | Theorems.Thm_PI_LocCartanPair_splPlane_herm
-- name    : PI.LocCartanPair.splPlane_herm
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:09:55.923316+00:00
-- url     : https://prove2.me/theorems/06b0c56d-8a20-4bf4-a1d8-24c13194010b
-- title:
--   Loc Cartan Pair: spl Plane herm
-- statement:
--   The Loc Cartan Pair construction uses the spl Plane herm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/SplPlane.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/SplPlane.lean#L16-L18

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

theorem PI.LocCartanPair.splPlane_herm {ι : Type} [Fintype ι] (A : Matrix ι ι R) (hA : Aᴴ = A) (a b : ι → R) :
    star (star a ⬝ᵥ (A *ᵥ b)) = star b ⬝ᵥ (A *ᵥ a) := by sorry
