-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_second_operator_mem_second_family
-- name    : PositivityTheory.Rg.Sw.LC.CoreC.second_operator_mem_second_family
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:57:27.193547+00:00
-- url     : https://prove2.me/theorems/268c4521-b7bb-4d39-ae58-b341cb80bff9
-- title:
--   Core C: second operator mem second family
-- statement:
--   The Core C construction uses the second operator mem second family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/SecondOperatorMemSecondFamily.lean#L27-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/SecondOperatorMemSecondFamily.lean#L27-L37

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_FunctionalRepresentationByContraction
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SecondOperatorMemSecondFamily
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

theorem PositivityTheory.Rg.Sw.LC.CoreC.second_operator_mem_second_family (ε : Fin m → Bool) (c : ℝ) (a b : Fin m) {g : PX m n} (hg : g ∈ F2 ε) : D2 ε c a b g ∈ F2 ε := by sorry
