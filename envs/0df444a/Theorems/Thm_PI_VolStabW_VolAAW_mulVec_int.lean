-- Prove2me | Theorems.Thm_PI_VolStabW_VolAAW_mulVec_int
-- name    : PI.VolStabW.VolAAW.mulVec_int
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:42:46.593021+00:00
-- url     : https://prove2.me/theorems/72caf2cb-33a3-5612-a46f-ab892ce8cb96
-- title:
--   Vol AAW: mul Vec int
-- statement:
--   The Vol AAW construction uses the mul Vec int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensVolB.lean#L101-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensVolB.lean#L101-L106

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensVolA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SdDual
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensVolB
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
variable [FiniteDimensional F E] (v : HeightOneSpectrum (𝓞 F))

theorem PI.VolStabW.VolAAW.mulVec_int {ι : Type} [Fintype ι] (A : Matrix ι ι F)
    (hA : ∀ i j, algebraMap F (Fv F v) (A i j) ∈ v.adicCompletionIntegers F)
    (w : ι → Fv F v) (hw : ∀ i, w i ∈ v.adicCompletionIntegers F) (i : ι) :
    (A.map (algebraMap F (Fv F v))).mulVec w i ∈ v.adicCompletionIntegers F := by sorry
