-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_exists_isIntegralElem_linear
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.exists_isIntegralElem_linear
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:23:25.9466+00:00
-- url     : https://prove2.me/theorems/eeb37dd9-7199-453d-b064-3d4434d00642
-- title:
--   Geo: exists is Integral Elem linear
-- statement:
--   The Geo construction uses the exists is Integral Elem linear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterGoodD.lean#L129-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterGoodD.lean#L129-L146

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactMore_Imports
import Definitions.Def_Lemmata_FirstBlockLemmaA_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodD
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

theorem ReciprocityTheory.ChartRestriction.G.Geo.exists_isIntegralElem_linear [Infinite k] {R : Type*} [CommRing R] [Algebra k R] {r : ℕ}
    (ℓ : Fin (r + 1) → R) (F : MvPolynomial (Fin (r + 1)) k) (hF : F ≠ 0) (h : aeval ℓ F = 0) :
    ∃ lam : Fin r → k, IntOver k (fun i => ℓ i.succ - lam i • ℓ 0) (ℓ 0) := by sorry
