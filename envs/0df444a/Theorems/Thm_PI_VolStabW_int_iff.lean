-- Prove2me | Theorems.Thm_PI_VolStabW_int_iff
-- name    : PI.VolStabW.int_iff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:56:02.028368+00:00
-- url     : https://prove2.me/theorems/e158b81d-5bbe-4d1d-8574-e716471ba0de
-- title:
--   Vol Stab W: int iff
-- statement:
--   The Vol Stab W construction uses the int iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensCntL.lean#L36-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensCntL.lean#L36-L49

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCntRes
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCntL
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
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

theorem PI.VolStabW.int_iff {ι ι' : Type} [Fintype ι] [Fintype ι'] (b : Module.Basis ι F E)
    (c : Module.Basis ι' F E)
    (hbc : ∀ j k, algebraMap F (Fv F v) (b.repr (c j) k) ∈ v.adicCompletionIntegers F)
    (hcb : ∀ k j, algebraMap F (Fv F v) (c.repr (b k) j) ∈ v.adicCompletionIntegers F)
    (z : Fv F v ⊗[F] E) :
    (∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr z k ∈ v.adicCompletionIntegers F) ↔
      (∀ j, (Algebra.TensorProduct.basis (Fv F v) c).repr z j ∈ v.adicCompletionIntegers F) := by sorry
