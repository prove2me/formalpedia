-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_Core_first_operator_preserves_first_family
-- name    : PositivityTheory.Rg.Sw.LC.Core.first_operator_preserves_first_family
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:55:19.042014+00:00
-- url     : https://prove2.me/theorems/6d1b1437-b57f-4b00-a0bf-d4b23d4d463c
-- title:
--   Core: first operator preserves first family
-- statement:
--   The Core construction uses the first operator preserves first family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/AdjoinFirstOperatorsPreservesFamily.lean#L73-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/AdjoinFirstOperatorsPreservesFamily.lean#L73-L86

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_FformSmulRight
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_AdjoinFirstOperatorsPreservesFamily
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.Core
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}

theorem PositivityTheory.Rg.Sw.LC.Core.first_operator_preserves_first_family (ε : Fin m → Bool) (c : ℝ) (a b : Fin m) (f : PX m n) (hf : f ∈ F1 ε) : D1 ε c a b f ∈ F1 ε := by sorry
