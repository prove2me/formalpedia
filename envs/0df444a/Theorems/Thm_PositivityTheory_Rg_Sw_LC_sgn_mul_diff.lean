-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_sgn_mul_diff
-- name    : PositivityTheory.Rg.Sw.LC.sgn_mul_diff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:49:22.711687+00:00
-- url     : https://prove2.me/theorems/e483345c-90af-478c-8df1-585da9a3cfba
-- title:
--   LC: sgn mul diff
-- statement:
--   The LC construction uses the sgn mul diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/HopPderivComm.lean#L58-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/HopPderivComm.lean#L58-L60

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullStableAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_HopPderivComm
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

theorem PositivityTheory.Rg.Sw.LC.sgn_mul_diff (ε : Fin m → Bool) {a b : Fin m} (h : ε a ≠ ε b) : sgn ε a * sgn ε b = -1 := by sorry
