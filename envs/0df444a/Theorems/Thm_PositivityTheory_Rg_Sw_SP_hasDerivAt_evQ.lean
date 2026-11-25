-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_SP_hasDerivAt_evQ
-- name    : PositivityTheory.Rg.Sw.SP.hasDerivAt_evQ
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T09:04:42.62146+00:00
-- url     : https://prove2.me/theorems/744caac8-1504-4759-a943-dc89c33fdf94
-- title:
--   SP: has Deriv At ev Q
-- statement:
--   The SP construction uses the has Deriv At ev Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/BridgeC.lean#L25-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/BridgeC.lean#L25-L34

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_BridgeB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_BridgeC
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

theorem PositivityTheory.Rg.Sw.SP.hasDerivAt_evQ (s z : ℂ) (x : MC n) (hx : x ∈ OmS s) (k l : Fin n) (Q : Fm n) :
    HasDerivAt (fun t : ℂ => evQ s z Q (x + t • eU k l))
      (∑ kk, evQ s z (MvPolynomial.pderiv kk Q) x * gD s x k l kk) 0 := by sorry
