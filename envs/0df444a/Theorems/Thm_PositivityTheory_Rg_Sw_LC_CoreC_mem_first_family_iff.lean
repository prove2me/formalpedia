-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_mem_first_family_iff
-- name    : PositivityTheory.Rg.Sw.LC.CoreC.mem_first_family_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:26:01.335473+00:00
-- url     : https://prove2.me/theorems/03a9d78e-c68a-48c0-ac02-b1fc5fc26bd2
-- title:
--   Core C: mem first family iff
-- statement:
--   The Core C construction uses the mem first family iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/PartialDerivZeroSecondFamily.lean#L30-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/PartialDerivZeroSecondFamily.lean#L30-L35

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoeffSmulX
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PartialDerivZeroSecondFamily
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finsupp
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw.LC.CoreC
open PositivityTheory.Rg.Sw G
variable {m n : ℕ}

theorem PositivityTheory.Rg.Sw.LC.CoreC.mem_first_family_iff (ε : Fin m → Bool) (p : PX m n) : p ∈ F1 ε ↔ ∀ s ∈ p.support, ∀ k ∈ s.support, inF1 ε k := by sorry
