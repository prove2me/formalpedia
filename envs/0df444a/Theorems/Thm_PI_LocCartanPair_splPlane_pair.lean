-- Prove2me | Theorems.Thm_PI_LocCartanPair_splPlane_pair
-- name    : PI.LocCartanPair.splPlane_pair
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:34:38.452042+00:00
-- url     : https://prove2.me/theorems/98441255-cd6a-46c9-abcf-30df316b84f1
-- title:
--   Loc Cartan Pair: spl Plane pair
-- statement:
--   The Loc Cartan Pair construction uses the spl Plane pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/SplPlane.lean#L136-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/SplPlane.lean#L136-L158

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
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable {R : Type} [CommRing R] [StarRing R]

theorem PI.LocCartanPair.splPlane_pair [IsLocalRing R] {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι R)
    (hA : Aᴴ = A) (x y : ι → R) (hxx : star x ⬝ᵥ (A *ᵥ x) = 0)
    (hxy : star x ⬝ᵥ (A *ᵥ y) = 1) :
    ∃ i₀ j₀, i₀ ≠ j₀ ∧ IsUnit (x i₀ * y j₀ - y i₀ * x j₀) := by sorry
