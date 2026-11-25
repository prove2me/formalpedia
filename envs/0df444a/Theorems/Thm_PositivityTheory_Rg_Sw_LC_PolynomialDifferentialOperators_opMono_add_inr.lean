-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialDifferentialOperators_opMono_add_inr
-- name    : PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators.opMono_add_inr
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:57:38.333801+00:00
-- url     : https://prove2.me/theorems/f6528095-17c1-4215-968f-775e7d7f2858
-- title:
--   Polynomial Differential Operators: op Mono add inr
-- statement:
--   The Polynomial Differential Operators construction uses the op Mono add inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/ComapDomainInlAdd.lean#L147-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/ComapDomainInlAdd.lean#L147-L156

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PairSym
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ComapDomainInlAdd
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
variable {m n : ℕ}

theorem PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators.opMono_add_inr (t : Ix m n ⊕ Ix m n →₀ ℕ) (k : Ix m n) (f : PX m n) :
    opMono (t + Finsupp.single (Sum.inr k) 1) f = opMono t (pderiv k f) := by sorry
