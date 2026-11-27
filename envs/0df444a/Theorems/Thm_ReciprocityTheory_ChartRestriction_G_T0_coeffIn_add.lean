-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_coeffIn_add
-- name    : ReciprocityTheory.ChartRestriction.G.T0.coeffIn_add
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-27T05:09:04.546628+00:00
-- url     : https://prove2.me/theorems/e261ab67-0464-5835-9531-aeb89f634082
-- title:
--   T0: coeff In add
-- statement:
--   The T0 construction uses the coeff In add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/CoeffEvWMem.lean#L20-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/CoeffEvWMem.lean#L20-L23

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SumLeSqrtCardMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_CoeffEvWMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open MvPolynomial
variable {R : Type*} [CommRing R] {B : Type*} [CommRing B] [Algebra R B] {D N : ℕ}
variable (W : Submodule R B)

theorem ReciprocityTheory.ChartRestriction.G.T0.coeffIn_add {m : ℕ} {p q : MvPolynomial (Fin (D + 2) × Fin (N + 1)) B}
    (hp : CoeffIn W m p) (hq : CoeffIn W m q) : CoeffIn W m (p + q) := by sorry
