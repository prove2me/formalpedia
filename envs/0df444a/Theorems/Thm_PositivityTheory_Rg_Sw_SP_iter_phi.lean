-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_SP_iter_phi
-- name    : PositivityTheory.Rg.Sw.SP.iter_phi
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:04:51.285314+00:00
-- url     : https://prove2.me/theorems/92d592bf-a197-4b4e-afa2-602a3099d8a5
-- title:
--   SP: iter phi
-- statement:
--   The SP construction uses the iter phi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/MinorFormula.lean#L91-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/MinorFormula.lean#L91-L97

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorIter
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorFormula
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP
open PositivityTheory.Rg.Sw.SP.Mi
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.SP.iter_phi (s : ℂ) (m : ℕ) (b : Bool) {ρ : ℕ} (I J : Fin ρ ↪ Fin n) (N : ℕ) (f : Pm (Polynomial ℂ) ρ) :
    (minorOp s m b I J)^[N] (phi b I J f) = ((-(cMn s b)) ^ ρ) ^ N • phi b I J ((detE (alMn m b))^[N] f) := by sorry
