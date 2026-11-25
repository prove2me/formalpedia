-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IntPf_coeff_cone
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.IntPf.coeff_cone
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:57:01.539465+00:00
-- url     : https://prove2.me/theorems/8aec1615-a7eb-4e23-a09e-05330cffecf8
-- title:
--   Int Pf: coeff cone
-- statement:
--   The Int Pf construction uses the coeff cone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/IntegralStatementPfA.lean#L34-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/IntegralStatementPfA.lean#L34-L43

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

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.IntPf.coeff_cone (a : ι → E) (f : MvPolynomial ι R) (n : ℕ) :
    (cone a f).coeff n = aeval a (homogeneousComponent n f) := by sorry
