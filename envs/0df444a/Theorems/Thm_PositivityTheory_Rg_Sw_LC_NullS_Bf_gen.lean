-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_NullS_Bf_gen
-- name    : PositivityTheory.Rg.Sw.LC.NullS.Bf_gen
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:49:04.465725+00:00
-- url     : https://prove2.me/theorems/da8ceba7-bf7e-4967-b1b5-3ee582a138e4
-- title:
--   Null S: Bf gen
-- statement:
--   The Null S construction uses the Bf gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/SumPderivXMem.lean#L131-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/SumPderivXMem.lean#L131-L134

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

theorem PositivityTheory.Rg.Sw.LC.NullS.Bf_gen (ε : Fin m → Bool) (i j k l k' l' : Fin n) :
    Bf ε i j (Qp ε k l) (Qp ε k' l') ∈ QA ε := by sorry
