-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_SP_Mi_deriv_prod
-- name    : PositivityTheory.Rg.Sw.SP.Mi.deriv_prod
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:59:28.949861+00:00
-- url     : https://prove2.me/theorems/961cac91-590b-4e79-9ef3-95acdf821c5a
-- title:
--   Mi: deriv prod
-- statement:
--   The Mi construction uses the deriv prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/MinorB.lean#L9-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/MinorB.lean#L9-L21

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorDefs
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorB
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP PositivityTheory.Rg.Sw.SP.Mi

theorem PositivityTheory.Rg.Sw.SP.Mi.deriv_prod {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (D : Derivation R A A) {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → A) : D (∏ i ∈ s, f i) = ∑ c ∈ s, (∏ i ∈ s.erase c, f i) * D (f c) := by sorry
