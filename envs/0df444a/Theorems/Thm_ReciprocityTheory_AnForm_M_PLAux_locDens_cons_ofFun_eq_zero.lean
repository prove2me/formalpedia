-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_PLAux_locDens_cons_ofFun_eq_zero
-- name    : ReciprocityTheory.AnForm.M.PLAux.locDens_cons_ofFun_eq_zero
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T09:19:19.114307+00:00
-- url     : https://prove2.me/theorems/0d6dfb62-82f4-4295-9add-81351ed688d1
-- title:
--   PLAux: loc Dens cons of Fun eq zero
-- statement:
--   The PLAux construction uses the loc Dens cons of Fun eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/HessCEqZeroOfEventuallyEqZero.lean#L85-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/HessCEqZeroOfEventuallyEqZero.lean#L85-L102

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

theorem ReciprocityTheory.AnForm.M.PLAux.locDens_cons_ofFun_eq_zero {A : FinHolAtlas (e + 1) X} (v : X → ℝ)
    (Φ : Fin e → LocPot X) (j : Fin A.n) {y : Fin (e + 1) → ℂ} (hy : y ∈ (A.chart j).target)
    (hv : (A.chart j).symm y ∉ tsupport v) :
    locDens A (Fin.cons (LocPot.ofFun v) Φ) j y = 0 := by sorry
