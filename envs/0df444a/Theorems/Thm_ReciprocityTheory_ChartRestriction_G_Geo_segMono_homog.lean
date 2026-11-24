-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_segMono_homog
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.segMono_homog
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:11:15.357534+00:00
-- url     : https://prove2.me/theorems/9dadbf91-675b-431f-b725-bf24dce00511
-- title:
--   Geo: seg Mono homog
-- statement:
--   The Geo construction uses the seg Mono homog property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterFib.lean#L20-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterFib.lean#L20-L27

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFibA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFibB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
  [∀ k, DecidableEq (ι k)]

theorem ReciprocityTheory.ChartRestriction.G.Geo.segMono_homog (i : (k : K) → ι k) :
    IsWeightedHomogeneous (blkW ι) (segMono ι i) (fun _ => 1) := by sorry
