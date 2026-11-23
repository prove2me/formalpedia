-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreBb_op_eq_sum_of_subset
-- name    : PositivityTheory.Rg.Sw.LC.CoreBb.op_eq_sum_of_subset
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:41:05.539804+00:00
-- url     : https://prove2.me/theorems/db37edd0-6876-4b86-b8c8-8c502af252b1
-- title:
--   Core Bb: op eq sum of subset
-- statement:
--   The Core Bb construction uses the op eq sum of subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/ProdMapPowSingle.lean#L79-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/ProdMapPowSingle.lean#L79-L83

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ProdMapPowSingle
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.CoreBb
open PositivityTheory.Rg.Sw
variable {m n : ℕ}

theorem PositivityTheory.Rg.Sw.LC.CoreBb.op_eq_sum_of_subset (s : Sym m n) (f : PX m n) (T : Finset ((Fin m × Fin n × Bool) ⊕ (Fin m × Fin n × Bool) →₀ ℕ))
    (hT : s.support ⊆ T) : op s f = ∑ t ∈ T, s.coeff t • opMono t f := by sorry
