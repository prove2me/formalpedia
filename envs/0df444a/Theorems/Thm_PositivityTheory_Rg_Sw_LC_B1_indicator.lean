-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_B1_indicator
-- name    : PositivityTheory.Rg.Sw.LC.B1.indicator
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:57:09.503018+00:00
-- url     : https://prove2.me/theorems/83736022-7aca-593a-9b51-fa28d543ee52
-- title:
--   B1: indicator
-- statement:
--   The B1 construction uses the indicator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/PderivPowMonomial.lean#L240-L313
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/PderivPowMonomial.lean#L240-L313

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PderivPowMonomial
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.B1
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}
local notation "σ" => Fin m × Fin n × Bool
variable (ε : Fin m → Bool)

theorem PositivityTheory.Rg.Sw.LC.B1.indicator (Γ : Finset (σ →₀ ℕ)) (hΓ : ∀ γ ∈ Γ, ∀ k ∈ γ.support, inF1 ε k) :
    ∀ N, ∀ γ ∈ Γ, (Γ.filter (γ < ·)).card ≤ N →
      ∃ P : Sym m n, SymbolInFirstFamily ε P ∧ ∀ δ ∈ Γ, op P (monomial δ 1) = if δ = γ then 1 else 0 := by sorry
