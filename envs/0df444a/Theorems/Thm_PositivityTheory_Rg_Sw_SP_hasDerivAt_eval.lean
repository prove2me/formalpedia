-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_SP_hasDerivAt_eval
-- name    : PositivityTheory.Rg.Sw.SP.hasDerivAt_eval
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:00:07.720206+00:00
-- url     : https://prove2.me/theorems/736f3af6-14b1-4283-a0e6-188302e12674
-- title:
--   SP: has Deriv At eval
-- statement:
--   The SP construction uses the has Deriv At eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/BridgeA.lean#L15-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/BridgeA.lean#L15-L50

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

theorem PositivityTheory.Rg.Sw.SP.hasDerivAt_eval {ι : Type} [Fintype ι] [DecidableEq ι] (g : ℂ → ι → ℂ) (g' : ι → ℂ)
    (hg : ∀ k, HasDerivAt (fun t => g t k) (g' k) 0) (P : MvPolynomial ι ℂ) :
    HasDerivAt (fun t => MvPolynomial.eval (g t) P)
      (∑ k, MvPolynomial.eval (g 0) (MvPolynomial.pderiv k P) * g' k) 0 := by sorry
