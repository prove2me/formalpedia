-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_comap_kill_variables_le
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.comap_kill_variables_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:10:34.757012+00:00
-- url     : https://prove2.me/theorems/e950550b-7a3c-5eeb-8a5a-93c2b3d95e8f
-- title:
--   Arakelov Geometry: comap kill variables le
-- statement:
--   The Arakelov Geometry construction uses the comap kill variables le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/TwoLeKrullDimOfRelevantPrime.lean#L118-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/TwoLeKrullDimOfRelevantPrime.lean#L118-L126

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CardPieceIrrelevantIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthCokerEqKerAddDimOneOrderSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_TwoLeKrullDimOfRelevantPrime
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

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.comap_kill_variables_le {ι : Fin 2 → Type} [∀ k, Fintype (ι k)] {q : Ideal (MRing ι)}
    (hh : IsMultiHomogIdeal q) :
    q.comap (i2kill (ι := ι) 0) ≤ q.comap ((i2kill (ι := ι) 1).comp (i2kill 0)) := by sorry
