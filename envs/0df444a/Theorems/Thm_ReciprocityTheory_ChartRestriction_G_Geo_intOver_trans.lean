-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_intOver_trans
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.intOver_trans
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:23:38.499638+00:00
-- url     : https://prove2.me/theorems/a62a719e-ba57-40f3-a419-c24137096d33
-- title:
--   Geo: int Over trans
-- statement:
--   The Geo construction uses the int Over trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterGoodE.lean#L11-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterGoodE.lean#L11-L43

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodD
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
noncomputable section
variable {k : Type*} [Field k]

theorem ReciprocityTheory.ChartRestriction.G.Geo.intOver_trans {R : Type*} [CommRing R] [Algebra k R] {r : ℕ} (ℓ : Fin (r + 1) → R)
    (lam : Fin r → k) (h0 : IntOver k (fun i => ℓ i.succ - lam i • ℓ 0) (ℓ 0)) {x : R}
    (hx : IntOver k ℓ x) : IntOver k (fun i => ℓ i.succ - lam i • ℓ 0) x := by sorry
