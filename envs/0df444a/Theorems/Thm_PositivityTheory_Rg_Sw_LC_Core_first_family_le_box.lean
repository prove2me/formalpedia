-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_Core_first_family_le_box
-- name    : PositivityTheory.Rg.Sw.LC.Core.first_family_le_box
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:54:57.150229+00:00
-- url     : https://prove2.me/theorems/90b20ab5-7d4f-5ee0-a4bc-bd355daadf67
-- title:
--   Core: first family le box
-- statement:
--   The Core construction uses the first family le box property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/MonomialMemSupported.lean#L27-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/MonomialMemSupported.lean#L27-L39

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_AdjoinFirstOperatorsPreservesFamily
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_MonomialMemSupported
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

theorem PositivityTheory.Rg.Sw.LC.Core.first_family_le_box (ε : Fin m → Bool) : F1 (n := n) ε ≤ box ε Set.univ := by sorry
