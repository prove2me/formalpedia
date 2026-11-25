-- Prove2me | Theorems.Thm_PI_VolStabW_goodV_aa
-- name    : PI.VolStabW.goodV_aa
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:44:50.595897+00:00
-- url     : https://prove2.me/theorems/ce16663b-d1c6-5f05-80ea-b489a9e1532a
-- title:
--   Vol Stab W: good V aa
-- statement:
--   The Vol Stab W construction uses the good V aa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensHH.lean#L156-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensHH.lean#L156-L178

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

theorem PI.VolStabW.goodV_aa (b : Module.Basis (Fin d) F E) (σ : E →ₐ[F] E) {M a : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (Tinv : Matrix (Fin a) (Fin a) E) :
    ∀ᶠ v in cofinite, GoodV b v σ J Tinv := by sorry
