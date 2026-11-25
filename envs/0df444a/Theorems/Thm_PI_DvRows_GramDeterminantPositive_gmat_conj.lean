-- Prove2me | Theorems.Thm_PI_DvRows_GramDeterminantPositive_gmat_conj
-- name    : PI.DvRows.GramDeterminantPositive.gmat_conj
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:29:05.591501+00:00
-- url     : https://prove2.me/theorems/e8eee0aa-85eb-401f-bcb1-dbc0912de26f
-- title:
--   Gram Determinant Positive: gmat conj
-- statement:
--   The Gram Determinant Positive construction uses the gmat conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/MulVecInjectiveOfKer.lean#L253-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/MulVecInjectiveOfKer.lean#L253-L256

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Pieces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_MulVecInjectiveOfKer
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
omit hC3

theorem PI.DvRows.GramDeterminantPositive.gmat_conj (φ : K →+* ℂ) {m : ℕ} (f : Fin m → A.V) :
    gmat A h (ComplexEmbedding.conjugate φ) f = (gmat A h φ f).map (starRingEnd ℂ) := by sorry
