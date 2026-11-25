-- Prove2me | Theorems.Thm_PI_VolStabSW_VolAAW_mem_latV_iff
-- name    : PI.VolStabSW.VolAAW.mem_latV_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:42:56.282998+00:00
-- url     : https://prove2.me/theorems/c79fe756-f9f8-4f8f-a334-e6da2730e678
-- title:
--   Vol AAW: mem lat V iff
-- statement:
--   The Vol AAW construction uses the mem lat V iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/LocDensVolB.lean#L93-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/LocDensVolB.lean#L93-L99

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensVolA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_SdDual
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensVolB
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
open PI.VolStabSW.VolAAW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes SdUniqW
  PositiveNearLattice SdDualW
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [Algebra F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E)
variable [FiniteDimensional F E] (v : HeightOneSpectrum (𝓞 F))

theorem PI.VolStabSW.VolAAW.mem_latV_iff {a M : ℕ} (Y : Fin a → Fin M → Fv F v ⊗[F] E) :
    Y ∈ latV (M := M) (n := a) b v ↔ ∀ q, cT b v Y q ∈ v.adicCompletionIntegers F := by sorry
