-- Prove2me | Theorems.Thm_PI_VolStabW_LatFactsW_smul_mem_latSub
-- name    : PI.VolStabW.LatFactsW.smul_mem_latSub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:55:55.995957+00:00
-- url     : https://prove2.me/theorems/a25dc3b9-8261-4869-a7d9-f40e90dbbebd
-- title:
--   Lat Facts W: smul mem lat Sub
-- statement:
--   The Lat Facts W construction uses the smul mem lat Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensHL.lean#L16-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensHL.lean#L16-L24

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_UnifVSpec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHL
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
open PI.VolStabW.LatFactsW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))

theorem PI.VolStabW.LatFactsW.smul_mem_latSub {a M : ℕ} {s : Fv F v} (hs : s ∈ v.adicCompletionIntegers F)
    {x : Fin a → Fin M → Fv F v ⊗[F] E} (hx : x ∈ latSub b v a M) : s • x ∈ latSub b v a M := by sorry
