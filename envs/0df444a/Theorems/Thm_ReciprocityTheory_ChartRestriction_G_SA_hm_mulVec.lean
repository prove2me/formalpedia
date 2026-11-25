-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hm_mulVec
-- name    : ReciprocityTheory.ChartRestriction.G.SA.hm_mulVec
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:34:02.090645+00:00
-- url     : https://prove2.me/theorems/5b255f67-5d21-4e38-9e42-654b5b1f1ecd
-- title:
--   SA: hm mul Vec
-- statement:
--   The SA construction uses the hm mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/UnitaryTransvectionZeroSecondMemClosure.lean#L18-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/UnitaryTransvectionZeroSecondMemClosure.lean#L18-L37

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

theorem ReciprocityTheory.ChartRestriction.G.SA.hm_mulVec (e f : ι → K) (M : Matrix (Fin 2) (Fin 2) K) (x : ι → K) :
    hm σ J e f M *ᵥ x = x + ((M 0 0 - 1) * hf σ J x f + M 0 1 * hf σ J x e) • e
      + (M 1 0 * hf σ J x f + (M 1 1 - 1) * hf σ J x e) • f := by sorry
