-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_holoOn_eval_lift
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.holoOn_eval_lift
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:23:42.720808+00:00
-- url     : https://prove2.me/theorems/a682539d-009f-5d0f-8304-a0418d01147b
-- title:
--   Geo: holo On eval lift
-- statement:
--   The Geo construction uses the holo On eval lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterRedC.lean#L48-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterRedC.lean#L48-L52

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedC
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
open MvPolynomial ReciprocityTheory.AnForm.M
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {P J : Ideal (MRing ι)} {e : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.Geo.holoOn_eval_lift (R : AnLogRes P J e) (x : R.X) (f : MRing ι) :
    R.A.HoloOn (R.U x) (fun y => eval (R.lift x y) (map (Int.castRingHom ℂ) f)) := by sorry
