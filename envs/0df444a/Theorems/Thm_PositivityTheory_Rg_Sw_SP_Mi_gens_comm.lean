-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_SP_Mi_gens_comm
-- name    : PositivityTheory.Rg.Sw.SP.Mi.gens_comm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:17:18.142887+00:00
-- url     : https://prove2.me/theorems/9e2ad33c-209b-47b6-9894-1e8c77bb781c
-- title:
--   Mi: gens comm
-- statement:
--   The Mi construction uses the gens comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/MinorCoreA.lean#L20-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/MinorCoreA.lean#L20-L22

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorCoreA
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

theorem PositivityTheory.Rg.Sw.SP.Mi.gens_comm (α : R) (ρ : ℕ) : ∀ a ∈ gens α ρ, ∀ b ∈ gens α ρ, a * b = b * a := by sorry
