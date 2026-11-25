-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_Basic_mapDomain_flp_flp
-- name    : PositivityTheory.Rg.Sw.LC.Basic.mapDomain_flp_flp
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:56:20.480058+00:00
-- url     : https://prove2.me/theorems/f841a9e2-67d0-5c3e-912f-628060678e6d
-- title:
--   Basic: map Domain flp flp
-- statement:
--   The Basic construction uses the map Domain flp flp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/MapDomainFlpFlp.lean#L127-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/MapDomainFlpFlp.lean#L127-L130

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullStableAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_MapDomainFlpFlp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.Basic
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}

theorem PositivityTheory.Rg.Sw.LC.Basic.mapDomain_flp_flp (t : Ix m n →₀ ℕ) : Finsupp.mapDomain flp (Finsupp.mapDomain flp t) = t := by sorry
