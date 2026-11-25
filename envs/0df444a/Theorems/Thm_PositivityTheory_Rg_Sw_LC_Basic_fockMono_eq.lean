-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_Basic_fockMono_eq
-- name    : PositivityTheory.Rg.Sw.LC.Basic.fockMono_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:40:41.64179+00:00
-- url     : https://prove2.me/theorems/2acca2af-f38e-4e65-9e95-77d72a764205
-- title:
--   Basic: fock Mono eq
-- statement:
--   The Basic construction uses the fock Mono eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/MapDomainFlpFlp.lean#L79-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/MapDomainFlpFlp.lean#L79-L81

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

theorem PositivityTheory.Rg.Sw.LC.Basic.fockMono_eq (c : ℝ) (s : Ix m n →₀ ℕ) :
    fockMono c s = ((phi c (monomial s 1) : CrAlg m n c) : Module.End ℂ (PX m n)) 1 := by sorry
