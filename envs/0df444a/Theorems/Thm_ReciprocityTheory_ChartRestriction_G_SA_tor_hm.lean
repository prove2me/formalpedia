-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_tor_hm
-- name    : ReciprocityTheory.ChartRestriction.G.SA.tor_hm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:11.951789+00:00
-- url     : https://prove2.me/theorems/eb28b076-1e39-4ae3-95aa-4bdf5bf0c142
-- title:
--   SA: tor hm
-- statement:
--   The SA construction uses the tor hm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/UnitaryTransvectionZeroSecondMemClosure.lean#L98-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/UnitaryTransvectionZeroSecondMemClosure.lean#L98-L101

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichAlongSub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_UnitaryTransvectionZeroSecondMemClosure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.SA
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] {σ : K →+* K}
  {J : Matrix ι ι K}
variable (σ J)

theorem ReciprocityTheory.ChartRestriction.G.SA.tor_hm (e f : ι → K) (l m : K) : tor σ J e f l m = hm σ J e f !![l, 0; 0, m] := by sorry
