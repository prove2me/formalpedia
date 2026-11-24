-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_tor_mulVec
-- name    : ReciprocityTheory.ChartRestriction.G.SA.tor_mulVec
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:08:49.874649+00:00
-- url     : https://prove2.me/theorems/e6eb4a5d-5d65-4bc7-96ca-0f44e9f2d4ca
-- title:
--   SA: tor mul Vec
-- statement:
--   The SA construction uses the tor mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/EichAlongSub.lean#L17-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/EichAlongSub.lean#L17-L26

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichPreserves
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichAlongSub
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
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R] {σ : R →+* R}
  {J : Matrix ι ι R}
variable (σ J)

theorem ReciprocityTheory.ChartRestriction.G.SA.tor_mulVec (e f : ι → R) (l m : R) (x : ι → R) :
    tor σ J e f l m *ᵥ x = x + ((l - 1) * hf σ J x f) • e + ((m - 1) * hf σ J x e) • f := by sorry
