-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_B1_sf_inr
-- name    : PositivityTheory.Rg.Sw.LC.B1.sf_inr
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:56:24.522654+00:00
-- url     : https://prove2.me/theorems/cedd7cc8-5a28-51af-8c06-89548945afdc
-- title:
--   B1: sf inr
-- statement:
--   The B1 construction uses the sf inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/PderivPowMonomial.lean#L232-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/PderivPowMonomial.lean#L232-L238

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

theorem PositivityTheory.Rg.Sw.LC.B1.sf_inr (γ : σ →₀ ℕ) (hγ : ∀ k ∈ γ.support, inF1 ε k) (c : ℂ) :
    SymbolInFirstFamily ε (monomial (Finsupp.mapDomain Sum.inr γ) c : Sym m n) := by sorry
