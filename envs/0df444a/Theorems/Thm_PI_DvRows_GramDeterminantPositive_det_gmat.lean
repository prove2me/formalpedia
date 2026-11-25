-- Prove2me | Theorems.Thm_PI_DvRows_GramDeterminantPositive_det_gmat
-- name    : PI.DvRows.GramDeterminantPositive.det_gmat
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:28:59.519088+00:00
-- url     : https://prove2.me/theorems/5bd550c6-6be2-4092-9953-1ea11c81a7db
-- title:
--   Gram Determinant Positive: det gmat
-- statement:
--   The Gram Determinant Positive construction uses the det gmat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/MulVecInjectiveOfKer.lean#L263-L272
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/MulVecInjectiveOfKer.lean#L263-L272

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Pieces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_MulVecInjectiveOfKer
import Theorems.Thm_Formalism_HN_HeightGram_det_gmat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.DvRows
open PI.DvRows.GramDeterminantPositive
open Matrix
open scoped ComplexOrder
open NumberField Formalism.BasicNotions PI.Dv
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable (A : HLat K) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K)
variable (hC1 : ∀ i j, IsCM (h (A.b i) (A.b j)))
  (hC3 : ∀ (v : InfinitePlace K) i j,
    Formalism.HermitianLatticesTheory.majAt A.b A.X v (A.b i) (A.b j) = v.embedding (h (A.b i) (A.b j)))
include hC3

theorem PI.DvRows.GramDeterminantPositive.det_gmat (φ : K →+* ℂ) {m : ℕ} (f : Fin m → A.V) :
    (gmat A h φ f).det = (Formalism.HN.gramPl A.b A.X (InfinitePlace.mk φ) f).det := by sorry
