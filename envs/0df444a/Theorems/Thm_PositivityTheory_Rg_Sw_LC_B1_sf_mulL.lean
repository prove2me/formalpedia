-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_B1_sf_mulL
-- name    : PositivityTheory.Rg.Sw.LC.B1.sf_mulL
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:40:13.074114+00:00
-- url     : https://prove2.me/theorems/053199bc-af46-4c2f-b8d7-ddb09b1672ae
-- title:
--   B1: sf mul L
-- statement:
--   The B1 construction uses the sf mul L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/PderivPowMonomial.lean#L217-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/PderivPowMonomial.lean#L217-L222

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

theorem PositivityTheory.Rg.Sw.LC.B1.sf_mulL (μ : σ →₀ ℕ) (hμ : ∀ k ∈ μ.support, inF1 ε k) {s : Sym m n} (h : SymbolInFirstFamily ε s) (c : ℂ) :
    SymbolInFirstFamily ε (monomial (Finsupp.mapDomain Sum.inl μ) c * s) := by sorry
