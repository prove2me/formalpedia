-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_Basic_coe_phi_monomial
-- name    : PositivityTheory.Rg.Sw.LC.Basic.coe_phi_monomial
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:57:04.161368+00:00
-- url     : https://prove2.me/theorems/cfc89f5c-0fd5-56e6-b17c-2db6b6382be3
-- title:
--   Basic: coe phi monomial
-- statement:
--   The Basic construction uses the coe phi monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/MapDomainFlpFlp.lean#L71-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/MapDomainFlpFlp.lean#L71-L77

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullStableAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_MapDomainFlpFlp
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.Basic
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}

theorem PositivityTheory.Rg.Sw.LC.Basic.coe_phi_monomial (c : ℝ) (s : Ix m n →₀ ℕ) :
    ((phi c (monomial s 1) : CrAlg m n c) : Module.End ℂ (PX m n)) =
      ((Finset.univ : Finset (Ix m n)).toList.map fun k => (cr c k) ^ (s k)).prod := by sorry
