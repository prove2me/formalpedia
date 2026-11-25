-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_P_mInt_update_eq
-- name    : ReciprocityTheory.AnForm.P.mInt_update_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:29:57.463285+00:00
-- url     : https://prove2.me/theorems/2444e05d-c2fc-469c-8ed6-cc7b3113bbd4
-- title:
--   P: m Int update eq
-- statement:
--   The P construction uses the m Int update eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/LeviForms/Energy.lean#L60-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/LeviForms/Energy.lean#L60-L63

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_IsRegFamilyInhabitStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Stokes
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_Energy
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.P
open MeasureTheory ReciprocityTheory.AnForm.M FinHolAtlas
noncomputable section

theorem ReciprocityTheory.AnForm.P.mInt_update_eq {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas (e + 1) X)
    (F : Fin (e + 1) → LocPot X) (k : Fin (e + 1)) (P : LocPot X) (g : X → ℝ) :
    mInt A (Function.update F k P) g = mInt A (Fin.cons P (Fin.tail (F ∘ Equiv.swap 0 k))) g := by sorry
