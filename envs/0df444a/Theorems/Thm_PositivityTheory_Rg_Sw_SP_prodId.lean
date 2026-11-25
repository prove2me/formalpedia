-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_SP_prodId
-- name    : PositivityTheory.Rg.Sw.SP.prodId
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:02:38.60889+00:00
-- url     : https://prove2.me/theorems/a48487f7-3cec-4994-a623-4f68f6aa03d1
-- title:
--   SP: prod Id
-- statement:
--   The SP construction uses the prod Id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/MinorFormula.lean#L99-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/MinorFormula.lean#L99-L108

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

theorem PositivityTheory.Rg.Sw.SP.prodId (a : Polynomial ℂ) (c : ℂ) (ρ N : ℕ) :
    Polynomial.C (((-c) ^ ρ) ^ N) * ∏ l ∈ Finset.range N, ∏ i ∈ Finset.range ρ, (a + (l : Polynomial ℂ) - (i : Polynomial ℂ)) =
      Polynomial.C ((c ^ ρ) ^ N) * ∏ l ∈ Finset.range N, ∏ i ∈ Finset.range ρ, (-a - Polynomial.C ((l : ℂ) - i)) := by sorry
