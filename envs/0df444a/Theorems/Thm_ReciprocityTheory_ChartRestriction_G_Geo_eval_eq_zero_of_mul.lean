-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_eval_eq_zero_of_mul
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.eval_eq_zero_of_mul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:37:59.879797+00:00
-- url     : https://prove2.me/theorems/6bd06272-6b6d-4c86-9f75-62fbffa16033
-- title:
--   Geo: eval eq zero of mul
-- statement:
--   The Geo construction uses the eval eq zero of mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterBridgeQ.lean#L11-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterBridgeQ.lean#L11-L58

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeO
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterPC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeQ
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

theorem ReciprocityTheory.ChartRestriction.G.Geo.eval_eq_zero_of_mul (hM : PCMinContractStatement) {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {e : ℕ} (hP : IsArithVar P (e + 1)) {u : MRing ι}
    (hu : u ∉ P) {H : MRingOver ℂ ι}
    (h : ∀ z ∈ mcPts P, eval z (map (Int.castRingHom ℂ) u) * eval z H = 0) :
    ∀ z ∈ mcPts P, eval z H = 0 := by sorry
