-- Prove2me | Theorems.Thm_PI_VolStabSW_OmFibG_gramFilt_zero
-- name    : PI.VolStabSW.OmFibG.gramFilt_zero
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:44:49.365182+00:00
-- url     : https://prove2.me/theorems/e43c2660-f8ef-5bcc-b6d8-1bd9028c7cc7
-- title:
--   Om Fib G: gram Filt zero
-- statement:
--   The Om Fib G construction uses the gram Filt zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HaarFibreUniqueness/FibExGram.lean#L244-L273
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HaarFibreUniqueness/FibExGram.lean#L244-L273

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensVDx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensVSec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_ExistsUnifFv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_FibExGram
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW PI.VolStabSW.OmFibG
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain Topology Filter
open scoped TensorProduct

theorem PI.VolStabSW.OmFibG.gramFilt_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (v : HeightOneSpectrum (𝓞 F)) (d : ℕ)
    (b : Module.Basis (Fin d) F E) (x : Fin 0 → Fin M → Fv F v ⊗[F] E) :
    FiltConcl σ hσ M J hJ 0 v d b x := by sorry
