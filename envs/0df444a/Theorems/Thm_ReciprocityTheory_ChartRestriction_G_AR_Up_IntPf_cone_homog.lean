-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IntPf_cone_homog
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.IntPf.cone_homog
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:56:50.865861+00:00
-- url     : https://prove2.me/theorems/45d3f4c4-7891-4b28-9632-030f34d1a400
-- title:
--   Int Pf: cone homog
-- statement:
--   The Int Pf construction uses the cone homog property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/IntegralStatementPfA.lean#L17-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/IntegralStatementPfA.lean#L17-L32

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

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.IntPf.cone_homog (a : ι → E) {f : MvPolynomial ι R} {d : ℕ} (hf : f.IsHomogeneous d) :
    cone a f = Polynomial.monomial d (aeval a f) := by sorry
