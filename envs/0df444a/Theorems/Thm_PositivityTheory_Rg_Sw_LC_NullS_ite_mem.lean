-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_NullS_ite_mem
-- name    : PositivityTheory.Rg.Sw.LC.NullS.ite_mem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:49:48.392725+00:00
-- url     : https://prove2.me/theorems/2336fe87-1a35-590d-ba92-9be95997414c
-- title:
--   Null S: ite mem
-- statement:
--   The Null S construction uses the ite mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/SumPderivXMem.lean#L125-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/SumPderivXMem.lean#L125-L129

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

theorem PositivityTheory.Rg.Sw.LC.NullS.ite_mem (ε : Fin m → Bool) (p : Prop) [Decidable p] (k l : Fin n) :
    (if p then (Qp ε k l : PX m n) else 0) ∈ QA ε := by sorry
