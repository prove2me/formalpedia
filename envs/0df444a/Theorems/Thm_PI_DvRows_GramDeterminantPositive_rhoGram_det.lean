-- Prove2me | Theorems.Thm_PI_DvRows_GramDeterminantPositive_rhoGram_det
-- name    : PI.DvRows.GramDeterminantPositive.rhoGram_det
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:22:21.807182+00:00
-- url     : https://prove2.me/theorems/a8e9615a-473d-41f4-93bf-31474cedd664
-- title:
--   Gram Determinant Positive: rho Gram det
-- statement:
--   The Gram Determinant Positive construction uses the rho Gram det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/MulVecInjectiveOfKer.lean#L282-L293
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/MulVecInjectiveOfKer.lean#L282-L293

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
include hC1

theorem PI.DvRows.GramDeterminantPositive.rhoGram_det (v : InfinitePlace K) {m : ℕ} (f : Fin m → A.V) :
    (((A.X v)⁻¹ * cmat A (rho v.embedding) f)ᴴ * ((A.X v)⁻¹ * cmat A (rho v.embedding) f)).det =
      (Formalism.HN.gramPl A.b A.X (InfinitePlace.mk (v.embedding.comp (starRingEnd K))) f).det := by sorry
