-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreBb_collapse
-- name    : PositivityTheory.Rg.Sw.LC.CoreBb.collapse
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:40:45.282677+00:00
-- url     : https://prove2.me/theorems/babe57fc-b3b5-4c8c-8848-4412326312b2
-- title:
--   Core Bb: collapse
-- statement:
--   The Core Bb construction uses the collapse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/ProdMapPowSingle.lean#L164-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/ProdMapPowSingle.lean#L164-L176

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

theorem PositivityTheory.Rg.Sw.LC.CoreBb.collapse (P : Fin m → Prop) [DecidablePred P] (c : Fin n) (b : Bool) (F : Fin m → PX m n)
    (k : Fin m × Fin n × Bool) :
    ∑ a ∈ Finset.univ.filter P, (if k = (a, c, b) then F a else 0) =
      if P k.1 ∧ k.2.1 = c ∧ k.2.2 = b then F k.1 else 0 := by sorry
