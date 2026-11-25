-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_SP_foldr_phi
-- name    : PositivityTheory.Rg.Sw.SP.foldr_phi
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:50:26.236875+00:00
-- url     : https://prove2.me/theorems/421b97b5-2cf3-4e76-82da-dfc0057fe1f3
-- title:
--   SP: foldr phi
-- statement:
--   The SP construction uses the foldr phi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/MinorFormula.lean#L75-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/MinorFormula.lean#L75-L82

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

theorem PositivityTheory.Rg.Sw.SP.foldr_phi (s : ℂ) (m : ℕ) (b : Bool) {ρ : ℕ} (I J : Fin ρ ↪ Fin n) (σ : Equiv.Perm (Fin ρ)) (L : List (Fin ρ))
    (f : Pm (Polynomial ℂ) ρ) :
    (L.foldr (fun k g => opH s m b (I k) (J (σ k)) ∘ₗ g) LinearMap.id) (phi b I J f) =
      (-(cMn s b)) ^ L.length • phi b I J ((L.foldr (fun k g => opE (alMn m b) k (σ k) ∘ₗ g) LinearMap.id) f) := by sorry
