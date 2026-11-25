-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreBb_symK_inl
-- name    : PositivityTheory.Rg.Sw.LC.CoreBb.symK_inl
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:56:09.819083+00:00
-- url     : https://prove2.me/theorems/7a251f15-1aa9-40b4-b77f-c6389f0433af
-- title:
--   Core Bb: sym K inl
-- statement:
--   The Core Bb construction uses the sym K inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/ProdMapPowSingle.lean#L233-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/ProdMapPowSingle.lean#L233-L236

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ProdMapPowSingle
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.CoreBb
open PositivityTheory.Rg.Sw
variable {m n : ℕ}

theorem PositivityTheory.Rg.Sw.LC.CoreBb.symK_inl (ε : Fin m → Bool) (i j : Fin n) (k : Fin m × Fin n × Bool) :
    symK ε i j (X (Sum.inl k)) = rename Sum.inl (KopL ε i j (X k)) := by sorry
