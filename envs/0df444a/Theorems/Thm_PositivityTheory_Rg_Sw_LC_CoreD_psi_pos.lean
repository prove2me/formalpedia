-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreD_psi_pos
-- name    : PositivityTheory.Rg.Sw.LC.CoreD.psi_pos
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:20:53.637318+00:00
-- url     : https://prove2.me/theorems/c30114e2-4edd-583c-bd8c-06aa1b334c7a
-- title:
--   Core D: psi pos
-- statement:
--   The Core D construction uses the psi pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/SymKEqZeroOfOm.lean#L53-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/SymKEqZeroOfOm.lean#L53-L68

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SymbolFirstFamilyOfMem
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SymKEqZeroOfOm
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

theorem PositivityTheory.Rg.Sw.LC.CoreD.psi_pos (p : Sym m n) (hp : p ≠ 0) : 0 < (psi p p).re := by sorry
