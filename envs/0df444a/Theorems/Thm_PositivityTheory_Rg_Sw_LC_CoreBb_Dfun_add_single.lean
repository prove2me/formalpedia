-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreBb_Dfun_add_single
-- name    : PositivityTheory.Rg.Sw.LC.CoreBb.Dfun_add_single
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:55:40.775569+00:00
-- url     : https://prove2.me/theorems/d8a5b883-9a77-5a8c-9ca4-b344b1a05a0c
-- title:
--   Core Bb: Dfun add single
-- statement:
--   The Core Bb construction uses the Dfun add single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/ProdMapPowSingle.lean#L61-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/ProdMapPowSingle.lean#L61-L63

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ProdMapPowSingle
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.CoreBb
open PositivityTheory.Rg.Sw
variable {m n : ℕ}

theorem PositivityTheory.Rg.Sw.LC.CoreBb.Dfun_add_single (e : Fin m × Fin n × Bool → ℕ) (k : Fin m × Fin n × Bool) :
    Dfun (fun i => e i + if i = k then 1 else 0) = Dfun e * ((pderiv (R := ℂ) k).toLinearMap : Module.End ℂ (PX m n)) := by sorry
