-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_partner_support_second_family
-- name    : PositivityTheory.Rg.Sw.LC.CoreC.partner_support_second_family
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:57:44.741284+00:00
-- url     : https://prove2.me/theorems/7e203bb8-676a-5d23-83e4-a496205609d3
-- title:
--   Core C: partner support second family
-- statement:
--   The Core C construction uses the partner support second family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/FunctionalRepresentationByContraction.lean#L98-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/FunctionalRepresentationByContraction.lean#L98-L103

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_XPderivMono
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_FunctionalRepresentationByContraction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finsupp
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw.LC.CoreC
open PositivityTheory.Rg.Sw G
variable {m n : ℕ}

theorem PositivityTheory.Rg.Sw.LC.CoreC.partner_support_second_family (ε : Fin m → Bool) {u : Fin m × Fin n × Bool →₀ ℕ} (hu : ∀ k ∈ u.support, inF1 ε k) :
    ∀ k ∈ (u.mapDomain pE).support, ¬ inF1 ε k := by sorry
