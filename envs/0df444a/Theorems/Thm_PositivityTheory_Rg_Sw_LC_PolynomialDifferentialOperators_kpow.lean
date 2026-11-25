-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialDifferentialOperators_kpow
-- name    : PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators.kpow
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:58:14.189714+00:00
-- url     : https://prove2.me/theorems/8275b60b-8c5c-40cd-9a19-c58851e5eac5
-- title:
--   Polynomial Differential Operators: kpow
-- statement:
--   The Polynomial Differential Operators construction uses the kpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/MapDomainInlInr.lean#L20-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/MapDomainInlInr.lean#L20-L51

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_FirstFamilySymbolMulVariablePow
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_MapDomainInlInr
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

theorem PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators.kpow {a : Ix m n} (ha : inF1 ε a) (b : ℕ) : ∀ (d : ℕ) (u : Sym m n), SymbolInFirstFamily ε u → EtaLe u d →
    ∃ r, Good ε d r ∧ ∀ g, op u (X a ^ b * g) = op (u * X (Sum.inl a) ^ b) g + op r g := by sorry
