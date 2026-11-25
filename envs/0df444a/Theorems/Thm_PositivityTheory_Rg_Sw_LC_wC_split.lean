-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_wC_split
-- name    : PositivityTheory.Rg.Sw.LC.wC_split
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:50:10.761299+00:00
-- url     : https://prove2.me/theorems/f6835109-5b1f-503c-b9f6-bc3ad42ce0fb
-- title:
--   LC: w C split
-- statement:
--   The LC construction uses the w C split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/ContrEqOfSubset.lean#L62-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/ContrEqOfSubset.lean#L62-L68

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_GaussianMomentRecurrence
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ContrEqOfSubset
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw
variable {m n : ℕ}

theorem PositivityTheory.Rg.Sw.LC.wC_split (c : ℝ) (s : Fin m × Fin n × Bool →₀ ℕ) (a : Fin m) (i : Fin n) :
    wC c s = hC c (s (a, i, false)) (s (a, i, true)) *
      ∏ x ∈ Finset.univ.erase (a, i), hC c (s (x.1, x.2, false)) (s (x.1, x.2, true)) := by sorry
