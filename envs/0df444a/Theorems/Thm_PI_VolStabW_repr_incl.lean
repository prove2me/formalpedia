-- Prove2me | Theorems.Thm_PI_VolStabW_repr_incl
-- name    : PI.VolStabW.repr_incl
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:53:45.069706+00:00
-- url     : https://prove2.me/theorems/10788000-fc45-5741-9850-94e9023a5b00
-- title:
--   Vol Stab W: repr incl
-- statement:
--   The Vol Stab W construction uses the repr incl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensCntL.lean#L119-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensCntL.lean#L119-L124

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
variable {σ : E →ₐ[F] E} (A : AntiB F E σ)

theorem PI.VolStabW.repr_incl (e : E) (j : Fin 2) :
    (Algebra.TensorProduct.basis (Fv F v) A.c).repr (inclR (Fv F v) e) j =
      algebraMap F (Fv F v) (A.c.repr e j) := by sorry
