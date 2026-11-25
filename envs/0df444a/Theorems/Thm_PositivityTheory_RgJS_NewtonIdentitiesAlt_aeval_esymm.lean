-- Prove2me | Theorems.Thm_PositivityTheory_RgJS_NewtonIdentitiesAlt_aeval_esymm
-- name    : PositivityTheory.RgJS.NewtonIdentitiesAlt.aeval_esymm
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:02:51.970797+00:00
-- url     : https://prove2.me/theorems/2ec168bd-8225-4d12-8d96-53a7412f1c24
-- title:
--   Newton Identities Alt: aeval esymm
-- statement:
--   The Newton Identities Alt construction uses the aeval esymm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/NewtonLowerBounds/NewtonIdentitiesLowDegree.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/NewtonLowerBounds/NewtonIdentitiesLowDegree.lean#L13-L14

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

theorem PositivityTheory.RgJS.NewtonIdentitiesAlt.aeval_esymm (a : A → ℂ) (j : ℕ) : aeval a (esymm A ℂ j) = ev a j := by sorry
