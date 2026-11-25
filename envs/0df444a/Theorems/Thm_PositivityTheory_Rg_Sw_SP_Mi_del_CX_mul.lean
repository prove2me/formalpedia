-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_SP_Mi_del_CX_mul
-- name    : PositivityTheory.Rg.Sw.SP.Mi.del_CX_mul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:00:21.969432+00:00
-- url     : https://prove2.me/theorems/e4ea701e-bf9d-42d8-880d-57e52ae2f6f3
-- title:
--   Mi: del CX mul
-- statement:
--   The Mi construction uses the del CX mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/MinorB.lean#L83-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/MinorB.lean#L83-L87

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

theorem PositivityTheory.Rg.Sw.SP.Mi.del_CX_mul {R : Type} [CommRing R] {ρ : ℕ} (p q : Fin ρ) (α : R) (a b : Fin ρ) (g : Pm R ρ) :
    del p q (C α * X (a, b) * g) = C α * (X (a, p) * X (q, b)) * g + C α * X (a, b) * del p q g := by sorry
