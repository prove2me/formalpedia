-- Prove2me | Theorems.Thm_PI_VolStabW_intA_sig
-- name    : PI.VolStabW.intA_sig
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:46:19.27509+00:00
-- url     : https://prove2.me/theorems/1d40029e-c61e-4bed-bc1d-a60532c7d2f1
-- title:
--   Vol Stab W: int A sig
-- statement:
--   The Vol Stab W construction uses the int A sig property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensHH.lean#L129-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensHH.lean#L129-L135

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensVDx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHH
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
  Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
variable {b v}

theorem PI.VolStabW.intA_sig (σ : E →ₐ[F] E)
    (hg : ∀ k m, algebraMap F (Fv F v) (b.repr (σ (b k)) m) ∈ v.adicCompletionIntegers F)
    {z : Fv F v ⊗[F] E} (hz : intA b v z) : intA b v (sigR (Fv F v) σ z) := by sorry
