-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreD_op_sum_sym
-- name    : PositivityTheory.Rg.Sw.LC.CoreD.op_sum_sym
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:25:36.750666+00:00
-- url     : https://prove2.me/theorems/efd48dbc-1e56-426f-86c6-c1c31ae17843
-- title:
--   Core D: op sum sym
-- statement:
--   The Core D construction uses the op sum sym property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/BoxLeFirstFamily.lean#L46-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/BoxLeFirstFamily.lean#L46-L51

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

theorem PositivityTheory.Rg.Sw.LC.CoreD.op_sum_sym {ι : Type*} (F : Finset ι) (g : ι → Sym m n) (f : PX m n) :
    op (∑ i ∈ F, g i) f = ∑ i ∈ F, op (g i) f := by sorry
