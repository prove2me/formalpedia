-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_B1_pderiv_pow_monomial
-- name    : PositivityTheory.Rg.Sw.LC.B1.pderiv_pow_monomial
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:56:34.785324+00:00
-- url     : https://prove2.me/theorems/f87ea0d7-c0a4-53c9-9d95-3d8895729591
-- title:
--   B1: pderiv pow monomial
-- statement:
--   The B1 construction uses the pderiv pow monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/PderivPowMonomial.lean#L15-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/PderivPowMonomial.lean#L15-L32

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

theorem PositivityTheory.Rg.Sw.LC.B1.pderiv_pow_monomial (i : σ) (e : ℕ) (s : σ →₀ ℕ) (a : ℂ) :
    (((pderiv (R := ℂ) i).toLinearMap ^ e) (monomial s a) : PX m n) =
      monomial (s - Finsupp.single i e) (a * ((s i).descFactorial e : ℂ)) := by sorry
