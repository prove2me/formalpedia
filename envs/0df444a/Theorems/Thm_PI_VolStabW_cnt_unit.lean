-- Prove2me | Theorems.Thm_PI_VolStabW_cnt_unit
-- name    : PI.VolStabW.cnt_unit
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T15:03:13.116129+00:00
-- url     : https://prove2.me/theorems/a4bbf639-f352-4581-9bec-a92bb937c68c
-- title:
--   Vol Stab W: cnt unit
-- statement:
--   The Vol Stab W construction uses the cnt unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensCnt.lean#L63-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensCnt.lean#L63-L84

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
  (hD : algebraMap F (Fv F v) A.D0 ∈ v.adicCompletionIntegers F)
variable {K : Type} [CommRing K] [Algebra (𝓞 F ⧸ v.asIdeal) K] (r : K)
  (hr : r * r = algebraMap _ K (red v (algebraMap F (Fv F v) A.D0)))
  (σ' : K ≃ₐ[𝓞 F ⧸ v.asIdeal] K) (hσr : σ' r = -r)

theorem PI.VolStabW.cnt_unit {n : ℕ} (G : Matrix (Fin n) (Fin n) E)
    (hG : ∀ p q j, algebraMap F (Fv F v) (A.c.repr (G p q) j) ∈ v.adicCompletionIntegers F)
    (u : E) (hu : G.det * u = 1)
    (hui : ∀ j, algebraMap F (Fv F v) (A.c.repr u j) ∈ v.adicCompletionIntegers F) :
    IsUnit ((entL v A hD G hG).map (rho v A hD r hr)).det := by sorry
