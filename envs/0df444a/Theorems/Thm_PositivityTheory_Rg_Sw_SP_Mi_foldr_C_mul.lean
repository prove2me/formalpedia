-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_SP_Mi_foldr_C_mul
-- name    : PositivityTheory.Rg.Sw.SP.Mi.foldr_C_mul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:00:13.700175+00:00
-- url     : https://prove2.me/theorems/b1cccf11-d535-42bc-a242-3c416ee3d0de
-- title:
--   Mi: foldr C mul
-- statement:
--   The Mi construction uses the foldr C mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/MinorIter.lean#L47-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/MinorIter.lean#L47-L52

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorCore
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorIter
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
variable {R : Type} [CommRing R] {ρ : ℕ}

theorem PositivityTheory.Rg.Sw.SP.Mi.foldr_C_mul (α : R) (r : R) (σ : Equiv.Perm (Fin ρ)) (L : List (Fin ρ)) (g : Pm R ρ) :
    (L.foldr (fun j h => opE α j (σ j) ∘ₗ h) LinearMap.id) (C r * g) =
      C r * (L.foldr (fun j h => opE α j (σ j) ∘ₗ h) LinearMap.id) g := by sorry
