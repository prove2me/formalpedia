-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_st_isPotential_cons
-- name    : ReciprocityTheory.AnForm.M.st_isPotential_cons
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:36:47.168626+00:00
-- url     : https://prove2.me/theorems/828b2b2e-7198-4249-b428-b8f5aad1250b
-- title:
--   M: st is Potential cons
-- statement:
--   The M construction uses the st is Potential cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/StokesA.lean#L95-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/StokesA.lean#L95-L104

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem ReciprocityTheory.AnForm.M.st_isPotential_cons (A : FinHolAtlas (e + 1) X) {u : X → ℝ} (hu : A.Smooth u)
    {Φ : Fin e → LocPot X} (hΦ : ∀ i, IsPotential A (Φ i)) :
    ∀ i, IsPotential A ((Fin.cons (LocPot.ofFun u) Φ : Fin (e + 1) → LocPot X) i) := by sorry
