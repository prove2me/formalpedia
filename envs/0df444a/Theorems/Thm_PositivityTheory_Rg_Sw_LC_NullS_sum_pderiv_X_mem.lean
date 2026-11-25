-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_NullS_sum_pderiv_X_mem
-- name    : PositivityTheory.Rg.Sw.LC.NullS.sum_pderiv_X_mem
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:49:47.38651+00:00
-- url     : https://prove2.me/theorems/4a20dd7b-dbc3-4ab0-a642-f152a49a28c0
-- title:
--   Null S: sum pderiv X mem
-- statement:
--   The Null S construction uses the sum pderiv X mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/SumPderivXMem.lean#L169-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/SumPderivXMem.lean#L169-L173

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PartialDerivQuadraticPairing
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SumPderivXMem
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.NullS
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}

theorem PositivityTheory.Rg.Sw.LC.NullS.sum_pderiv_X_mem (ε : Fin m → Bool) (R : PX m n) (hR : R ∈ QA ε) (f : Fin m → Fin m × Fin n × Bool)
    (g : Fin m → Fin m × Fin n × Bool) : (∑ a, R * pderiv (f a) (X (g a) : PX m n)) ∈ QA ε := by sorry
