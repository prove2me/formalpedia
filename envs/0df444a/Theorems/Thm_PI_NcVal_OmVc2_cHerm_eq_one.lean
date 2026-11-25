-- Prove2me | Theorems.Thm_PI_NcVal_OmVc2_cHerm_eq_one
-- name    : PI.NcVal.OmVc2.cHerm_eq_one
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:18:08.860692+00:00
-- url     : https://prove2.me/theorems/fd5a7ce9-ef95-5dd0-8e19-c8e4ae9edae6
-- title:
--   Om Vc2: c Herm eq one
-- statement:
--   The Om Vc2 construction uses the c Herm eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ValuationLocalVolumes/MulTupDiagonal.lean#L111-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ValuationLocalVolumes/MulTupDiagonal.lean#L111-L131

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SiegelWeilVolume_AddEquivAddHaarCharEqOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ValuationLocalVolumes_MulTupDiagonal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.NcVal PI.NcVal.OmVc2
open MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.DegenerateSiegelWeil.Scale PI.VolStabSW PI.VolStabSW.TensAllW
open scoped NNReal TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M n : ℕ} (R : Type) [CommRing R] [Algebra F R]
  [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [T2Space R]
  [SecondCountableTopology R]

theorem PI.NcVal.OmVc2.cHerm_eq_one [SecondCountableTopology (HermR R σ n)] (d : Fin n → (R ⊗[F] E)ˣ)
    (π : Equiv.Perm (Fin n)) (hπ : ∀ i, π (π i) = i) (hd : ∀ i, d (π i) = (d i)⁻¹) :
    cHerm σ hσ R (diagUnit d) = 1 := by sorry
