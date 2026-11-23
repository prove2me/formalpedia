-- Prove2me | Theorems.Thm_PI_VolStabSW_SdDualW_pairHerm_iota
-- name    : PI.VolStabSW.SdDualW.pairHerm_iota
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:15:09.551247+00:00
-- url     : https://prove2.me/theorems/d93add9c-6a95-49ef-93df-aebbb1196eb2
-- title:
--   Sd Dual W: pair Herm iota
-- statement:
--   The Sd Dual W construction uses the pair Herm iota property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/SdDual.lean#L402-L428
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/SdDual.lean#L402-L428

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_SdUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_PosNear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensAll
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_SdDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open PI.VolStabSW.SdDualW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW PositiveNearLattice SdUniqW
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
variable {E : Type} [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)
variable [FiniteDimensional F E]

theorem PI.VolStabSW.SdDualW.pairHerm_iota (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {a : ℕ}
    (X : Fin a → Fin a → Fv F v ⊗[F] E) (T : HermR (Fv F v) σ a) :
    pairHerm (Fv F v) σ a ⟨iota v σ X, iota_mem v σ hσ X⟩ T =
      BR (Fv F v) σ (1 : Matrix (Fin a) (Fin a) E) X
        (fun p i => (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i p) := by sorry
