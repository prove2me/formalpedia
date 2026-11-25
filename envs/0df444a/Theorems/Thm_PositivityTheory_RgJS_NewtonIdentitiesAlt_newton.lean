-- Prove2me | Theorems.Thm_PositivityTheory_RgJS_NewtonIdentitiesAlt_newton
-- name    : PositivityTheory.RgJS.NewtonIdentitiesAlt.newton
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:49:58.893788+00:00
-- url     : https://prove2.me/theorems/18ded743-0bba-4a4d-ab97-2cf2669395d2
-- title:
--   Newton Identities Alt: newton
-- statement:
--   The Newton Identities Alt construction uses the newton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/NewtonLowerBounds/NewtonIdentitiesLowDegree.lean#L21-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/NewtonLowerBounds/NewtonIdentitiesLowDegree.lean#L21-L25

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NewtonLow
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NewtonLowerBounds_NewtonIdentitiesLowDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open PositivityTheory PositivityTheory.RgJS PositivityTheory.RgJS.NewtonIdentitiesAlt
variable {A : Type} [Fintype A]

theorem PositivityTheory.RgJS.NewtonIdentitiesAlt.newton [DecidableEq A] (a : A → ℂ) (j : ℕ) :
    (j : ℂ) * ev a j = (-1) ^ (j + 1) *
      ∑ x ∈ antidiagonal j with x.1 < j, (-1) ^ x.1 * ev a x.1 * ∑ i, a i ^ x.2 := by sorry
