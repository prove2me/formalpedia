-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_comap_killB_mono
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.comap_killB_mono
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:10:12.200808+00:00
-- url     : https://prove2.me/theorems/481e0c7e-e538-53a9-9aff-9d323d44e7dd
-- title:
--   Arakelov Geometry: comap kill B mono
-- statement:
--   The Arakelov Geometry construction uses the comap kill B mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/NotRelevantOfDimZero.lean#L86-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/NotRelevantOfDimZero.lean#L86-L91

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_HasympAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_NotRelevantOfDimZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.comap_killB_mono {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) {T T' : Finset K}
    (h : T ⊆ T') : P.comap (killB T) ≤ P.comap (killB T') := by sorry
