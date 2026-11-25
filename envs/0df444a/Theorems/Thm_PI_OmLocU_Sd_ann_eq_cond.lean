-- Prove2me | Theorems.Thm_PI_OmLocU_Sd_ann_eq_cond
-- name    : PI.OmLocU.Sd.ann_eq_cond
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:06:54.93871+00:00
-- url     : https://prove2.me/theorems/dd68e7fe-5544-59e0-9e8f-5fb79e04c5c2
-- title:
--   Sd: ann eq cond
-- statement:
--   The Sd construction uses the ann eq cond property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalUnitaryOrbits/VolSqMulIndex.lean#L74-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalUnitaryOrbits/VolSqMulIndex.lean#L74-L89

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_SdUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensHI
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnitaryOrbits_VolSqMulIndex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OmLocU PI.OmLocU.Sd
open MeasureTheory PI.VolStabSW.SdUniqW Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem PI.OmLocU.Sd.ann_eq_cond {V : Type} (ψ0 : Fv F v → ℂ) (d : Fv F v) (B : V → V → Fv F v) (L : Set V)
    (hC : ∀ t : Fv F v, (∀ s ∈ v.adicCompletionIntegers F, ψ0 (s * t) = 1) ↔
      d * t ∈ v.adicCompletionIntegers F)
    (hs : ∀ s ∈ v.adicCompletionIntegers F, ∀ x ∈ L, ∃ x' ∈ L, ∀ y, B x' y = s * B x y) :
    ann (fun x y => ψ0 (B x y)) L = {y | ∀ x ∈ L, d * B x y ∈ v.adicCompletionIntegers F} := by sorry
