-- Prove2me | Theorems.Thm_PI_VolStabW_VolAAW_hform_single
-- name    : PI.VolStabW.VolAAW.hform_single
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:42:09.352817+00:00
-- url     : https://prove2.me/theorems/181fa51f-547b-509c-a39b-044090d30e49
-- title:
--   Vol AAW: hform single
-- statement:
--   The Vol AAW construction uses the hform single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensVolB.lean#L18-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensVolB.lean#L18-L30

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensVolA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SdDual
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensVolB
import Theorems.Thm_Formalism_UG_P_hform_single

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
open PI.VolStabW.VolAAW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes SdUniqW
  PositiveNearLattice SdDualW
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [Algebra F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E)

theorem PI.VolStabW.VolAAW.hform_single {A : Type} [CommRing A] {M : ℕ} (s : A →+* A) (Am : Matrix (Fin M) (Fin M) A)
    (i j : Fin M) (x y : A) :
    Formalism.UG.hform s Am (Pi.single i x) (Pi.single j y) = s x * Am i j * y := by sorry
