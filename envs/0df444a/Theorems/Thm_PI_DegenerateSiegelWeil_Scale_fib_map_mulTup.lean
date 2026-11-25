-- Prove2me | Theorems.Thm_PI_DegenerateSiegelWeil_Scale_fib_map_mulTup
-- name    : PI.DegenerateSiegelWeil.Scale.fib_map_mulTup
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:59:52.777419+00:00
-- url     : https://prove2.me/theorems/35fab22f-7113-5da6-8177-bb403682ec7c
-- title:
--   Scale: fib map mul Tup
-- statement:
--   The Scale construction uses the fib map mul Tup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SiegelWeilVolume/AddEquivAddHaarCharEqOne.lean#L91-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SiegelWeilVolume/AddEquivAddHaarCharEqOne.lean#L91-L115

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SiegelWeilVolume_MulTupApplyEqSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SiegelWeilVolume_AddEquivAddHaarCharEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.DegenerateSiegelWeil PI.DegenerateSiegelWeil.Scale
open MeasureTheory Topology Set Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolStabSW PI.VolStabSW.TensAllW
open scoped ENNReal NNReal TensorProduct Matrix
variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
  (hJ : ∀ i j, σ (J j i) = J i j) {n : ℕ} (R : Type) [CommRing R] [Algebra F R]
  [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [T2Space R]
  [SecondCountableTopology R] [SecondCountableTopology (HermR R σ n)]
include hJ

theorem PI.DegenerateSiegelWeil.Scale.fib_map_mulTup (hG : GramMulTup) (hU : IsOpen {r : R | IsUnit r}) (hL : LIP R)
    (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n))
    [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    (fib : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E))
    (hfib : IsFibreFamily μ (gramR R σ J) Subtype.val {X | LinearIndependent (R ⊗[F] E) X} ν
      univ fib)
    (D : (Matrix (Fin n) (Fin n) (R ⊗[F] E))ˣ) (S₀ : HermR R σ n)
    (hS₀ : hermMap R σ hσ (D : Matrix (Fin n) (Fin n) (R ⊗[F] E)) S₀ = S₀) :
    (fib S₀).map (mulTup (D : Matrix (Fin n) (Fin n) (R ⊗[F] E))) =
      ((cTup (M := M) R D : ℝ≥0∞) *
        (cHerm σ hσ R D : ℝ≥0∞)) • fib S₀ := by sorry
