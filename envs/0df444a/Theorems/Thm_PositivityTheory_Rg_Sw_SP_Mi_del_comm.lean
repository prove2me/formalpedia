-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_SP_Mi_del_comm
-- name    : PositivityTheory.Rg.Sw.SP.Mi.del_comm
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:59:48.362958+00:00
-- url     : https://prove2.me/theorems/5da9dca9-3434-4a2d-8790-5f237f81aa81
-- title:
--   Mi: del comm
-- statement:
--   The Mi construction uses the del comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/MinorB.lean#L89-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/MinorB.lean#L89-L97

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

theorem PositivityTheory.Rg.Sw.SP.Mi.del_comm {R : Type} [CommRing R] {ρ : ℕ} (p q p' q' : Fin ρ) (g : Pm R ρ) :
    del p q (del p' q' g) = del p' q' (del p q g) := by sorry
