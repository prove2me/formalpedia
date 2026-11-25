-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IntPf_eval_mul_homog
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.IntPf.eval_mul_homog
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:57:13.232913+00:00
-- url     : https://prove2.me/theorems/cfa29b4c-4173-49f8-a680-67b3c267eb33
-- title:
--   Int Pf: eval mul homog
-- statement:
--   The Int Pf construction uses the eval mul homog property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/IntegralStatementPfA.lean#L54-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/IntegralStatementPfA.lean#L54-L56

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CapelliComplements_FirstLemmaA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IntegralStatementPfA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.IntPf
noncomputable section
open MvPolynomial
variable {R E : Type*} [CommRing R] [CommRing E] [Algebra R E] {ι : Type*}

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.IntPf.eval_mul_homog {K : Type*} [CommRing K] (q : ι → K) (t : K) {G : MvPolynomial ι K} {m : ℕ}
    (hG : G.IsHomogeneous m) : eval (fun i => q i * t) G = t ^ m * eval q G := by sorry
