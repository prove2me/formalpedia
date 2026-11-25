-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_SP_derPart_apply
-- name    : PositivityTheory.Rg.Sw.SP.derPart_apply
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:51:34.806389+00:00
-- url     : https://prove2.me/theorems/b214158f-b68d-54d1-974f-d5a484dc1e0b
-- title:
--   SP: der Part apply
-- statement:
--   The SP construction uses the der Part apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/BridgeA.lean#L75-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/BridgeA.lean#L75-L83

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_BridgeH
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_DetSqSplit
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_BridgeA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP
open PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.SP.derPart_apply (s : ℂ) (b : Bool) (k l : Fin n) (Q : Fm n) :
    derPart s b k l Q = ∑ a : Fin n, ∑ d : Fin n, MvPolynomial.C (Polynomial.C (-(cB s b))) *
      (yv b a k * yv b l d * MvPolynomial.pderiv (b, a, d) Q) := by sorry
