-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_SP_Mi_detE_eq_sum
-- name    : PositivityTheory.Rg.Sw.SP.Mi.detE_eq_sum
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:59:34.196581+00:00
-- url     : https://prove2.me/theorems/54cbf2a6-af2f-4f44-931c-7a09a16c3d86
-- title:
--   Mi: det E eq sum
-- statement:
--   The Mi construction uses the det E eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/MinorCore.lean#L30-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/MinorCore.lean#L30-L35

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorCoreA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorCore
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP PositivityTheory.Rg.Sw.SP.Mi
variable {R : Type} [CommRing R]

theorem PositivityTheory.Rg.Sw.SP.Mi.detE_eq_sum (α : R) (ρ : ℕ) :
    detE α = ∑ σ : Equiv.Perm (Fin ρ), ((Equiv.Perm.sign σ : ℤ) : R) •
      ((List.finRange ρ).map (fun k => opE α k (σ k))).prod := by sorry
