-- Prove2me | Theorems.Thm_PI_OmFibreUniq_W_densAll_gen
-- name    : PI.OmFibreUniq.W.densAll_gen
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:16:32.045316+00:00
-- url     : https://prove2.me/theorems/ff803670-cb32-4cee-a6a3-315600029f63
-- title:
--   W: dens All gen
-- statement:
--   The W construction uses the dens All gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HaarFibreUniqueness/GramMapFibreExistence.lean#L16-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HaarFibreUniqueness/GramMapFibreExistence.lean#L16-L58

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_FibExGram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FreeOpen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensVTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_GramMapFibreExistence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OmFibreUniq PI.OmFibreUniq.W
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain Topology
open PI.OmFibreUniq PI.VolStabSW PI.VolStabSW.TensAllW PI.VolStabSW.OmFibG
open scoped TensorProduct

theorem PI.OmFibreUniq.W.densAll_gen {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (hdet : J.det ≠ 0) (v : HeightOneSpectrum (𝓞 F)) (a : ℕ)
    (μ : Measure (Fin a → Fin n → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ a))
    (hμ : μ.IsAddHaarMeasure) (hν : ν.IsAddHaarMeasure) :
    DensAll μ (gramR (Fv F v) σ J) Subtype.val ν
      {X : Fin a → Fin n → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} := by sorry
