-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_locDens_cons_add
-- name    : ReciprocityTheory.AnForm.M.locDens_cons_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:22:56.064797+00:00
-- url     : https://prove2.me/theorems/b4f03c86-34d8-4c76-b33c-d0dea1170710
-- title:
--   M: loc Dens cons add
-- statement:
--   The M construction uses the loc Dens cons add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/PotentialContDiffAt.lean#L44-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/PotentialContDiffAt.lean#L44-L55

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

theorem ReciprocityTheory.AnForm.M.locDens_cons_add (A : FinHolAtlas (e + 1) X) (P Q : LocPot X) (Φ : Fin e → LocPot X)
    (hP : IsPotential A P) (hQ : IsPotential A Q) (j : Fin A.n) {y : Fin (e + 1) → ℂ}
    (hy : y ∈ (A.chart j).target) :
    locDens A (Fin.cons (P + Q) Φ) j y =
      locDens A (Fin.cons P Φ) j y + locDens A (Fin.cons Q Φ) j y := by sorry
