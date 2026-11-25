-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_Core_box_mono
-- name    : PositivityTheory.Rg.Sw.LC.Core.box_mono
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:04:11.527842+00:00
-- url     : https://prove2.me/theorems/bf4a754c-e391-5574-a0f9-302b78e56844
-- title:
--   Core: box mono
-- statement:
--   The Core construction uses the box mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/MonomialMemSupported.lean#L41-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/MonomialMemSupported.lean#L41-L45

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_AdjoinFirstOperatorsPreservesFamily
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_MonomialMemSupported
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.Core
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}

theorem PositivityTheory.Rg.Sw.LC.Core.box_mono (ε : Fin m → Bool) {R R' : Set (Fin m → ℕ)} (h : R ⊆ R') : box (n := n) ε R ≤ box ε R' := by sorry
