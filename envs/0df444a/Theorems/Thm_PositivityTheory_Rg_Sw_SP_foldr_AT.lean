-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_SP_foldr_AT
-- name    : PositivityTheory.Rg.Sw.SP.foldr_AT
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:49:33.936824+00:00
-- url     : https://prove2.me/theorems/56a9afec-fd58-4604-92fe-c407709f8a31
-- title:
--   SP: foldr AT
-- statement:
--   The SP construction uses the foldr AT property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/CayDivA.lean#L172-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/CayDivA.lean#L172-L176

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivA
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
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.SP.foldr_AT {ρ : ℕ} (f : Fin ρ → Fm n →ₗ[ℂ] Fm n) (hf : ∀ k Q, Q ∈ AT n → f k Q ∈ AT n) (L : List (Fin ρ))
    {Q : Fm n} (hQ : Q ∈ AT n) : (L.foldr (fun k g => f k ∘ₗ g) LinearMap.id) Q ∈ AT n := by sorry
