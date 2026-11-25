-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialDifferentialOperators_mem_support_pderiv
-- name    : PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators.mem_support_pderiv
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:59:25.206033+00:00
-- url     : https://prove2.me/theorems/b78f4043-9edb-594c-862b-0e84e4506b71
-- title:
--   Polynomial Differential Operators: mem support pderiv
-- statement:
--   The Polynomial Differential Operators construction uses the mem support pderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/FirstFamilySymbolMulVariablePow.lean#L74-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/FirstFamilySymbolMulVariablePow.lean#L74-L91

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ComapDomainInlAdd
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_FirstFamilySymbolMulVariablePow
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ} {ε : Fin m → Bool}

theorem PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators.mem_support_pderiv {u : Sym m n} {i : Ix m n ⊕ Ix m n} {t' : Ix m n ⊕ Ix m n →₀ ℕ}
    (h : t' ∈ (pderiv i u).support) : ∃ t ∈ u.support, t i ≠ 0 ∧ t = t' + Finsupp.single i 1 := by sorry
