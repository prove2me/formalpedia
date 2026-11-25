-- Prove2me | Theorems.Thm_PI_LocCartanPair_splPlane
-- name    : PI.LocCartanPair.splPlane
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:34:26.038868+00:00
-- url     : https://prove2.me/theorems/54ae7653-11ca-4019-bace-e34e7dc971f3
-- title:
--   Loc Cartan Pair: spl Plane
-- statement:
--   The Loc Cartan Pair construction uses the spl Plane property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/SplPlane.lean#L178-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/SplPlane.lean#L178-L195

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

theorem PI.LocCartanPair.splPlane [IsLocalRing R] {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (hc : Fintype.card κ + 2 = Fintype.card ι) (A : Matrix ι ι R) (hA : Aᴴ = A)
    (x y : ι → R) (hxx : star x ⬝ᵥ (A *ᵥ x) = 0) (hyy : star y ⬝ᵥ (A *ᵥ y) = 0)
    (hxy : star x ⬝ᵥ (A *ᵥ y) = 1) :
    ∃ (u : Matrix ι (Fin 2 ⊕ κ) R) (v : Matrix (Fin 2 ⊕ κ) ι R) (A₁ : Matrix κ κ R),
      u * v = 1 ∧ v * u = 1 ∧ (∀ i, u i (.inl 0) = x i) ∧ (∀ i, u i (.inl 1) = y i) ∧
      uᴴ * A * u = fromBlocks !![0, 1; 1, 0] 0 0 A₁ ∧ A₁ᴴ = A₁ ∧
      (IsUnit A.det → IsUnit A₁.det) := by sorry
