-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_Basic_Sm_succ
-- name    : PositivityTheory.Rg.Sw.LC.Basic.Sm_succ
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:56:49.658562+00:00
-- url     : https://prove2.me/theorems/e9bd7940-7d7c-40de-8fc1-66ecc3c60bfa
-- title:
--   Basic: Sm succ
-- statement:
--   The Basic construction uses the Sm succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/MapDomainFlpFlp.lean#L189-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/MapDomainFlpFlp.lean#L189-L193

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

theorem PositivityTheory.Rg.Sw.LC.Basic.Sm_succ (c : ℝ) (s : Ix m n →₀ ℕ) (k : Ix m n) :
    Sm c (s + Finsupp.single k 1) = (2 * c : ℂ) • (X (flp k) * Sm c s) := by sorry
