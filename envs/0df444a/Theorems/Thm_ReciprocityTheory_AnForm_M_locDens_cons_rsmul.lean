-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_locDens_cons_rsmul
-- name    : ReciprocityTheory.AnForm.M.locDens_cons_rsmul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:19:33.773508+00:00
-- url     : https://prove2.me/theorems/3b501e68-4c62-41f6-a19a-e6c2218fe3eb
-- title:
--   M: loc Dens cons rsmul
-- statement:
--   The M construction uses the loc Dens cons rsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/PotentialContDiffAt.lean#L35-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/PotentialContDiffAt.lean#L35-L42

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCIsHermitian
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
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
open scoped ContDiff ComplexOrder
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem ReciprocityTheory.AnForm.M.locDens_cons_rsmul (A : FinHolAtlas (e + 1) X) (c : ℝ) (P : LocPot X)
    (Φ : Fin e → LocPot X) (j : Fin A.n) (y : Fin (e + 1) → ℂ) :
    locDens A (Fin.cons (P.rsmul c) Φ) j y = c * locDens A (Fin.cons P Φ) j y := by sorry
