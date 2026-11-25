-- Prove2me | Theorems.Thm_PI_VolStabW_intA_mul
-- name    : PI.VolStabW.intA_mul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:43:33.922282+00:00
-- url     : https://prove2.me/theorems/3aaff282-4f47-4c10-9cfd-99dd77fbd938
-- title:
--   Vol Stab W: int A mul
-- statement:
--   The Vol Stab W construction uses the int A mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensHH.lean#L113-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensHH.lean#L113-L119

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

theorem PI.VolStabW.intA_mul (hg : ∀ k l m, algebraMap F (Fv F v) (b.repr (b k * b l) m) ∈
      v.adicCompletionIntegers F)
    {z w : Fv F v ⊗[F] E} (hz : intA b v z) (hw : intA b v w) : intA b v (z * w) := by sorry
