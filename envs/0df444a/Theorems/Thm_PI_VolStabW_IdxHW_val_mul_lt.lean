-- Prove2me | Theorems.Thm_PI_VolStabW_IdxHW_val_mul_lt
-- name    : PI.VolStabW.IdxHW.val_mul_lt
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:46:31.06075+00:00
-- url     : https://prove2.me/theorems/f1c17e6c-d2f0-5455-82b9-3b43eff492ae
-- title:
--   Idx HW: val mul lt
-- statement:
--   The Idx HW construction uses the val mul lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensIdxE.lean#L19-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensIdxE.lean#L19-L23

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensIdxD
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensIdxE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW
  IsLocalRing
open PI.VolStabW.IdxHW
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  (b : Module.Basis (Fin 2) F E) (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E) (a : ℕ)

theorem PI.VolStabW.IdxHW.val_mul_lt {x y : Fv F v} (hx : x ∈ v.adicCompletionIntegers F) (hy : Valued.v y < 1) :
    Valued.v (x * y) < 1 := by sorry
