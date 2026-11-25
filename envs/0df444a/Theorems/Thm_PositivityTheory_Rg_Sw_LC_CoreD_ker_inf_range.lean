-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreD_ker_inf_range
-- name    : PositivityTheory.Rg.Sw.LC.CoreD.ker_inf_range
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:21:08.555913+00:00
-- url     : https://prove2.me/theorems/48bff32b-f0ad-45f6-964e-7d7fe802aab3
-- title:
--   Core D: ker inf range
-- statement:
--   The Core D construction uses the ker inf range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/SymKEqZeroOfOm.lean#L126-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/SymKEqZeroOfOm.lean#L126-L136

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

theorem PositivityTheory.Rg.Sw.LC.CoreD.ker_inf_range {N : ℕ} (v : S (n := n) ε N) (h0 : OmS ε N v = 0) (h1 : ∃ u, OmS ε N u = v) : v = 0 := by sorry
