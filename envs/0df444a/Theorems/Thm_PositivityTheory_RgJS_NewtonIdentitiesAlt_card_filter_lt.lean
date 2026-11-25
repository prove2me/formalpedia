-- Prove2me | Theorems.Thm_PositivityTheory_RgJS_NewtonIdentitiesAlt_card_filter_lt
-- name    : PositivityTheory.RgJS.NewtonIdentitiesAlt.card_filter_lt
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:02:56.996479+00:00
-- url     : https://prove2.me/theorems/f531b5af-6c54-55fe-b33a-497da74009bd
-- title:
--   Newton Identities Alt: card filter lt
-- statement:
--   The Newton Identities Alt construction uses the card filter lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/NewtonLowerBounds/NewtonIdentitiesLowDegree.lean#L28-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/NewtonLowerBounds/NewtonIdentitiesLowDegree.lean#L28-L40

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
omit [Fintype A]

theorem PositivityTheory.RgJS.NewtonIdentitiesAlt.card_filter_lt (j : ℕ) : #{x ∈ antidiagonal j | x.1 < j} ≤ j := by sorry
