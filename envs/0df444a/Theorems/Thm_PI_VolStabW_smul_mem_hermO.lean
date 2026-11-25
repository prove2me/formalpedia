-- Prove2me | Theorems.Thm_PI_VolStabW_smul_mem_hermO
-- name    : PI.VolStabW.smul_mem_hermO
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:45:11.860282+00:00
-- url     : https://prove2.me/theorems/5be320ed-b4b3-4e47-9d96-8b6ed6f42e1b
-- title:
--   Vol Stab W: smul mem herm O
-- statement:
--   The Vol Stab W construction uses the smul mem herm O property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensHI.lean#L57-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensHI.lean#L57-L69

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHI
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

theorem PI.VolStabW.smul_mem_hermO {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
    (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E) (a : ℕ)
    {s : Fv F v} (hs : s ∈ v.adicCompletionIntegers F) {S : HermR (Fv F v) σ a}
    (hS : S ∈ hermO b v σ a) : s • S ∈ hermO b v σ a := by sorry
