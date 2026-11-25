-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_SP_divZ_of_rcp
-- name    : PositivityTheory.Rg.Sw.SP.divZ_of_rcp
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:49:24.922687+00:00
-- url     : https://prove2.me/theorems/503ba106-f443-4ef4-ac21-85c511ae1724
-- title:
--   SP: div Z of rcp
-- statement:
--   The SP construction uses the div Z of rcp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/CayDivA.lean#L74-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/CayDivA.lean#L74-L76

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

theorem PositivityTheory.Rg.Sw.SP.divZ_of_rcp {T : Fm n →ₗ[ℂ] Fm n} (hT : RCP T) {i : ℕ} {Q : Fm n} (hQ : DivZ i Q) : DivZ i (T Q) := by sorry
