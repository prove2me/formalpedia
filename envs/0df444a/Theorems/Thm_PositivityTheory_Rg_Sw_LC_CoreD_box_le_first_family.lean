-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreD_box_le_first_family
-- name    : PositivityTheory.Rg.Sw.LC.CoreD.box_le_first_family
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:26:27.129075+00:00
-- url     : https://prove2.me/theorems/7bca99ad-23b4-429f-b941-4ff4fdd312c3
-- title:
--   Core D: box le first family
-- statement:
--   The Core D construction uses the box le first family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/BoxLeFirstFamily.lean#L53-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/BoxLeFirstFamily.lean#L53-L58

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SymKEqZeroOfOm
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_BoxLeFirstFamily
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
open PositivityTheory.Rg.Sw.LC.CoreD
variable {m n : ℕ} {ε : Fin m → Bool}

theorem PositivityTheory.Rg.Sw.LC.CoreD.box_le_first_family (R : Set (Fin m → ℕ)) : box (n := n) ε R ≤ F1 ε := by sorry
