-- Prove2me | Theorems.Thm_P2M_RH_PI_VolStabW_sigR_incl_8cb196a35df3e148
-- name    : P2M_RH_PI_VolStabW_sigR_incl_8cb196a35df3e148
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T15:02:43.741052+00:00
-- url     : https://prove2.me/theorems/5b882f59-5f8d-4a06-8c63-900f68e39200
-- title:
--   P2 M RH PI Vol Stab W sig R incl 8cb196a35df3e148: P2 M RH PI Vol Stab W sig R incl 8cb196a35df3e148
-- statement:
--   The P2 M RH PI Vol Stab W sig R incl 8cb196a35df3e148 construction uses the P2 M RH PI Vol Stab W sig R incl 8cb196a35df3e148 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensCnt.lean#L19-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensCnt.lean#L19-L22

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCntL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCntD
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCntQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCnt
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
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) {σ : E →ₐ[F] E} (A : AntiB F E σ)

theorem P2M_RH_PI_VolStabW_sigR_incl_8cb196a35df3e148 (e : E) : sigR (Fv F v) σ (inclR (Fv F v) e) = inclR (Fv F v) (σ e) := by sorry

alias «PI».«VolStabW».«sigR_incl» := P2M_RH_PI_VolStabW_sigR_incl_8cb196a35df3e148
