-- Prove2me | Theorems.Thm_PI_VolStabSW_smul_mem_hermO
-- name    : PI.VolStabSW.smul_mem_hermO
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:47:39.567653+00:00
-- url     : https://prove2.me/theorems/618c6c50-6427-4496-87f3-159e4af45014
-- title:
--   Vol Stab SW: smul mem herm O
-- statement:
--   The Vol Stab SW construction uses the smul mem herm O property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/LocDensHI.lean#L57-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/LocDensHI.lean#L57-L69

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensHL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensHI
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
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW

theorem PI.VolStabSW.smul_mem_hermO {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
    (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E) (a : ℕ)
    {s : Fv F v} (hs : s ∈ v.adicCompletionIntegers F) {S : HermR (Fv F v) σ a}
    (hS : S ∈ hermO b v σ a) : s • S ∈ hermO b v σ a := by sorry
