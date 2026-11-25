-- Prove2me | Theorems.Thm_PositivityTheory_KReal_Harm_first_lowering_commute_lowering
-- name    : PositivityTheory.KReal.Harm.first_lowering_commute_lowering
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:39:06.715831+00:00
-- url     : https://prove2.me/theorems/be29403a-649a-5121-adb0-d5b480e47e49
-- title:
--   Harm: first lowering commute lowering
-- statement:
--   The Harm construction uses the first lowering commute lowering property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreHarm.lean#L173-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreHarm.lean#L173-L183

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreLie
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreHarm
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
open PositivityTheory.KReal.Harm
variable {p q r s : ℕ}

theorem PositivityTheory.KReal.Harm.first_lowering_commute_lowering (a b : Ix p q) (c d : Ix r s) :
    Commute (low1 (r := r) (s := s) a b) (PI.FockOneDegW.lowOp (p := p) (q := q) c d) := by sorry
