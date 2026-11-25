-- Prove2me | Theorems.Thm_PositivityTheory_KReal_shift_neg_eq
-- name    : PositivityTheory.KReal.shift_neg_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:23:51.155671+00:00
-- url     : https://prove2.me/theorems/9a4f765a-4a1f-4468-973a-2c1a444b3b05
-- title:
--   KReal: shift neg eq
-- statement:
--   The KReal construction uses the shift neg eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreShape.lean#L89-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreShape.lean#L89-L97

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDefs
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreShape
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace
open PositivityTheory PositivityTheory.KReal

theorem PositivityTheory.KReal.shift_neg_eq (p q r s n m : ℕ) (hq : q ≤ r) (hp : p ≤ s) :
    shiftNu (cPair p q) (laNeg p q r s n m) =
      ofBlocks (pad [] (r - q) (List.replicate q (-(n : ℤ)))) (pad [] (s - p) (List.replicate p (-(m : ℤ)))) := by sorry
