-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_st_locDens_cons_eq_zero
-- name    : ReciprocityTheory.AnForm.M.st_locDens_cons_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:18:46.231111+00:00
-- url     : https://prove2.me/theorems/a5b144d1-5cac-49bf-b155-ad6344ed575d
-- title:
--   M: st loc Dens cons eq zero
-- statement:
--   The M construction uses the st loc Dens cons eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/StokesA.lean#L68-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/StokesA.lean#L68-L80

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

theorem ReciprocityTheory.AnForm.M.st_locDens_cons_eq_zero (A : FinHolAtlas (e + 1) X) (k : Fin A.n) (ψ : X → ℝ)
    (Φ : Fin e → LocPot X) {y : Fin (e + 1) → ℂ} (hy : y ∈ (A.chart k).target)
    (hψ : (A.chart k).symm y ∉ tsupport ψ) :
    locDens A (Fin.cons (LocPot.ofFun ψ) Φ) k y = 0 := by sorry
