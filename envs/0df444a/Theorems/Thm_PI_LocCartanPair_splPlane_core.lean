-- Prove2me | Theorems.Thm_PI_LocCartanPair_splPlane_core
-- name    : PI.LocCartanPair.splPlane_core
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:34:19.285568+00:00
-- url     : https://prove2.me/theorems/e8a050a8-76aa-5c7a-b9e7-cad16ce4ef96
-- title:
--   Loc Cartan Pair: spl Plane core
-- statement:
--   The Loc Cartan Pair construction uses the spl Plane core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/SplPlane.lean#L38-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/SplPlane.lean#L38-L130

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

theorem PI.LocCartanPair.splPlane_core (E : Fin 2 ⊕ κ ≃ ι) (A : Matrix ι ι R) (hA : Aᴴ = A) (x y : ι → R)
    (hxx : star x ⬝ᵥ (A *ᵥ x) = 0) (hyy : star y ⬝ᵥ (A *ᵥ y) = 0)
    (hxy : star x ⬝ᵥ (A *ᵥ y) = 1)
    (hdet : IsUnit (x (E (.inl 0)) * y (E (.inl 1)) - y (E (.inl 0)) * x (E (.inl 1)))) :
    ∃ (u : Matrix ι (Fin 2 ⊕ κ) R) (v : Matrix (Fin 2 ⊕ κ) ι R) (A₁ : Matrix κ κ R),
      u * v = 1 ∧ v * u = 1 ∧ (∀ i, u i (.inl 0) = x i) ∧ (∀ i, u i (.inl 1) = y i) ∧
      uᴴ * A * u = fromBlocks !![0, 1; 1, 0] 0 0 A₁ ∧ A₁ᴴ = A₁ ∧
      (IsUnit A.det → IsUnit A₁.det) := by sorry
