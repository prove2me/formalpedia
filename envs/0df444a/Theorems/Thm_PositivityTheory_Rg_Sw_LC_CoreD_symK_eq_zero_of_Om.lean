-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreD_symK_eq_zero_of_Om
-- name    : PositivityTheory.Rg.Sw.LC.CoreD.symK_eq_zero_of_Om
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:20:58.61154+00:00
-- url     : https://prove2.me/theorems/88883f60-0557-5b66-9673-ecca5ffa0193
-- title:
--   Core D: sym K eq zero of Om
-- statement:
--   The Core D construction uses the sym K eq zero of Om property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/SymKEqZeroOfOm.lean#L112-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/SymKEqZeroOfOm.lean#L112-L124

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
variable (hadj : ∀ (i j : Fin n) (s t : Sym m n), psi (symK ε i j s) t = psi s (symK ε j i t))
include hadj

theorem PositivityTheory.Rg.Sw.LC.CoreD.symK_eq_zero_of_Om (a : Sym m n) (h : Om ε a = 0) (i j : Fin n) : symK ε i j a = 0 := by sorry
