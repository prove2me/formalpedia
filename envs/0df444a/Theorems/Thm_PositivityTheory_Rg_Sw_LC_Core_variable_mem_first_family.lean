-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_Core_variable_mem_first_family
-- name    : PositivityTheory.Rg.Sw.LC.Core.variable_mem_first_family
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:55:10.636102+00:00
-- url     : https://prove2.me/theorems/98a099a0-e901-5cc3-9c06-f788805f945c
-- title:
--   Core: variable mem first family
-- statement:
--   The Core construction uses the variable mem first family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/AdjoinFirstOperatorsPreservesFamily.lean#L39-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/AdjoinFirstOperatorsPreservesFamily.lean#L39-L40

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

theorem PositivityTheory.Rg.Sw.LC.Core.variable_mem_first_family (ε : Fin m → Bool) {k : Fin m × Fin n × Bool} (hk : inF1 ε k) : (X k : PX m n) ∈ F1 ε := by sorry
