-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_Basic_fock_sum
-- name    : PositivityTheory.Rg.Sw.LC.Basic.fock_sum
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:56:11.121005+00:00
-- url     : https://prove2.me/theorems/3f98238f-2a5e-51be-baab-40224790d266
-- title:
--   Basic: fock sum
-- statement:
--   The Basic construction uses the fock sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/MapDomainFlpFlp.lean#L104-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/MapDomainFlpFlp.lean#L104-L109

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

theorem PositivityTheory.Rg.Sw.LC.Basic.fock_sum (c : ℝ) {ι : Type*} (t : Finset ι) (f : ι → PX m n) :
    fock c (∑ i ∈ t, f i) = ∑ i ∈ t, fock c (f i) := by sorry
