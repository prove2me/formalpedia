-- Prove2me | Theorems.Thm_PI_VolStabSW_OmFibG_dxOpen_gen
-- name    : PI.VolStabSW.OmFibG.dxOpen_gen
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:43:12.84589+00:00
-- url     : https://prove2.me/theorems/265fa75d-f728-4d92-b530-a7cf399e18af
-- title:
--   Om Fib G: dx Open gen
-- statement:
--   The Om Fib G construction uses the dx Open gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HaarFibreUniqueness/FibExGram.lean#L33-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HaarFibreUniqueness/FibExGram.lean#L33-L88

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

theorem PI.VolStabSW.OmFibG.dxOpen_gen {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (hdet : J.det ≠ 0) (a : ℕ) (v : HeightOneSpectrum (𝓞 F))
    (d : ℕ) (b : Module.Basis (Fin d) F E) (x : Fin a → Fin M → Fv F v ⊗[F] E)
    (hx : LinearIndependent (Fv F v ⊗[F] E) x) :
    IsOpen ((fun W => gramH (Fv F v) σ hσ J hJ (x + W) - gramH (Fv F v) σ hσ J hJ x -
      gramH (Fv F v) σ hσ J hJ W) '' (latSub b v a M : Set (Fin a → Fin M → Fv F v ⊗[F] E))) := by sorry
