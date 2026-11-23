-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_PLAux_isCompact_symm_image
-- name    : ReciprocityTheory.AnForm.M.PLAux.isCompact_symm_image
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:38:21.163649+00:00
-- url     : https://prove2.me/theorems/6f83cae3-cc31-43a7-8423-eca2faec6714
-- title:
--   PLAux: is Compact symm image
-- statement:
--   The PLAux construction uses the is Compact symm image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/HessCEqZeroOfEventuallyEqZero.lean#L160-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/HessCEqZeroOfEventuallyEqZero.lean#L160-L163

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCEqZeroOfEventuallyEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.M.PLAux
open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem ReciprocityTheory.AnForm.M.PLAux.isCompact_symm_image {ψ : OpenPartialHomeomorph X (Fin e → ℂ)} {F : (Fin e → ℂ) → ℝ}
    (hK : IsCompact (tsupport F)) (hKt : tsupport F ⊆ ψ.target) :
    IsCompact (ψ.symm '' tsupport F) := by sorry
