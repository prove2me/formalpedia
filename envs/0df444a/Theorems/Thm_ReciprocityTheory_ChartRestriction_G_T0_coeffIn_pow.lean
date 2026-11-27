-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_coeffIn_pow
-- name    : ReciprocityTheory.ChartRestriction.G.T0.coeffIn_pow
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-27T05:17:49.4898+00:00
-- url     : https://prove2.me/theorems/a9247124-e1a8-594a-b786-af858ac8f59d
-- title:
--   T0: coeff In pow
-- statement:
--   The T0 construction uses the coeff In pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/CoeffEvWMem.lean#L36-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/CoeffEvWMem.lean#L36-L42

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

theorem ReciprocityTheory.ChartRestriction.G.T0.coeffIn_pow {m : ℕ} {p : MvPolynomial (Fin (D + 2) × Fin (N + 1)) B}
    (hp : CoeffIn W m p) (k : ℕ) : CoeffIn W (m * k) (p ^ k) := by sorry
