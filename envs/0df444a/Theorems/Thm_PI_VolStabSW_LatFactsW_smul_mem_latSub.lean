-- Prove2me | Theorems.Thm_PI_VolStabSW_LatFactsW_smul_mem_latSub
-- name    : PI.VolStabSW.LatFactsW.smul_mem_latSub
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:43:24.134423+00:00
-- url     : https://prove2.me/theorems/2e8a3a25-3a84-45bc-8d34-a01b4b46e910
-- title:
--   Lat Facts W: smul mem lat Sub
-- statement:
--   The Lat Facts W construction uses the smul mem lat Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/LocDensHL.lean#L16-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/LocDensHL.lean#L16-L23

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_UnifVSpec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensHL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open PI.VolStabSW.LatFactsW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))

theorem PI.VolStabSW.LatFactsW.smul_mem_latSub {a M : ℕ} {s : Fv F v} (hs : s ∈ v.adicCompletionIntegers F)
    {x : Fin a → Fin M → Fv F v ⊗[F] E} (hx : x ∈ latSub b v a M) : s • x ∈ latSub b v a M := by sorry
