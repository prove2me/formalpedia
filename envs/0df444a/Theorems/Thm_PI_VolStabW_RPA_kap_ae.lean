-- Prove2me | Theorems.Thm_PI_VolStabW_RPA_kap_ae
-- name    : PI.VolStabW.RPA.kap_ae
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:41:33.819628+00:00
-- url     : https://prove2.me/theorems/3453fcad-e513-5798-b128-f4e31490b4d8
-- title:
--   RPA: kap ae
-- statement:
--   The RPA construction uses the kap ae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/ESSymmApply.lean#L145-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/ESSymmApply.lean#L145-L162

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProdSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_ESSymmApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.RPA
open MeasureTheory Filter Finset
open scoped NNReal ENNReal
variable {ι : Type} {W : ι → Type} [∀ i, MeasurableSpace (W i)]
variable (m : ∀ i, Measure (W i)) (L : ∀ i, Set (W i))
variable {m L}
variable (m L)
variable [∀ i, SigmaFinite (m i)]
variable {m L}

theorem PI.VolStabW.RPA.kap_ae [Countable ι] (hLm : ∀ i, MeasurableSet (L i)) (S : Finset ι) :
    ∀ᵐ x ∂kap m L S, ∀ i, (i ∈ S → x i ∉ L i) ∧ (i ∉ S → x i ∈ L i) := by sorry
