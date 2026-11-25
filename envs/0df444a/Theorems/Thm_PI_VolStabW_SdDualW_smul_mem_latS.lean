-- Prove2me | Theorems.Thm_PI_VolStabW_SdDualW_smul_mem_latS
-- name    : PI.VolStabW.SdDualW.smul_mem_latS
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:50:37.953537+00:00
-- url     : https://prove2.me/theorems/d40e2b84-f192-524f-a2d1-657f3dacba62
-- title:
--   Sd Dual W: smul mem lat S
-- statement:
--   The Sd Dual W construction uses the smul mem lat S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/SdDual.lean#L340-L345
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/SdDual.lean#L340-L345

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SdUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_PosNear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TensAll
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SdDual
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
open PI.VolStabW.SdDualW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW PositiveNearLattice SdUniqW
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
variable {E : Type} [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)
variable [FiniteDimensional F E]

theorem PI.VolStabW.SdDualW.smul_mem_latS (σ : E →ₐ[F] E) {s : Fv F v} (hs : s ∈ v.adicCompletionIntegers F)
    {z : Fv F v ⊗[F] E} (hz : z ∈ latS v b σ) : s • z ∈ latS v b σ := by sorry
