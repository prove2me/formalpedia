-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_B1_list_pderiv
-- name    : PositivityTheory.Rg.Sw.LC.B1.list_pderiv
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:56:18.820129+00:00
-- url     : https://prove2.me/theorems/5eb951d6-d93e-438c-a484-a1df29393b41
-- title:
--   B1: list pderiv
-- statement:
--   The B1 construction uses the list pderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/PderivPowMonomial.lean#L44-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/PderivPowMonomial.lean#L44-L66

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

theorem PositivityTheory.Rg.Sw.LC.B1.list_pderiv (γ : σ → ℕ) (l : List σ) (hl : l.Nodup) (s : σ →₀ ℕ) (a : ℂ) :
    ((l.map fun k => (pderiv (R := ℂ) k).toLinearMap ^ (γ k)).prod (monomial s a) : PX m n) =
      monomial (s - (l.map fun k => Finsupp.single k (γ k)).sum)
        (a * (l.map fun k => ((s k).descFactorial (γ k) : ℂ)).prod) := by sorry
