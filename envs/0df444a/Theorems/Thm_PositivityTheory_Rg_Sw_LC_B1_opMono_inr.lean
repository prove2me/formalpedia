-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_B1_opMono_inr
-- name    : PositivityTheory.Rg.Sw.LC.B1.opMono_inr
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:58:47.512856+00:00
-- url     : https://prove2.me/theorems/64d96e36-6d72-444c-80a9-57f9cc7c28d6
-- title:
--   B1: op Mono inr
-- statement:
--   The B1 construction uses the op Mono inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/PderivPowMonomial.lean#L157-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/PderivPowMonomial.lean#L157-L171

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

theorem PositivityTheory.Rg.Sw.LC.B1.opMono_inr (γ δ : σ →₀ ℕ) :
    opMono (Finsupp.mapDomain Sum.inr γ) (monomial δ 1 : PX m n) =
      monomial (δ - γ) (∏ k, ((δ k).descFactorial (γ k) : ℂ)) := by sorry
