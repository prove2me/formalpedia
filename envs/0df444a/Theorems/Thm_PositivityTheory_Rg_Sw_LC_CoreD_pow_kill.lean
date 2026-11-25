-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreD_pow_kill
-- name    : PositivityTheory.Rg.Sw.LC.CoreD.pow_kill
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:21:36.839962+00:00
-- url     : https://prove2.me/theorems/7eb80f10-e229-49b1-ac07-38a622658c63
-- title:
--   Core D: pow kill
-- statement:
--   The Core D construction uses the pow kill property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/SymKEqZeroOfOm.lean#L138-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/SymKEqZeroOfOm.lean#L138-L144

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

theorem PositivityTheory.Rg.Sw.LC.CoreD.pow_kill {N : ℕ} (k : ℕ) (v : S (n := n) ε N) (h : (OmS ε N ^ (k + 1)) v = 0) : OmS ε N v = 0 := by sorry
