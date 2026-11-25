-- Prove2me | Theorems.Thm_PositivityTheory_KReal_Harm_rename_first_lowering
-- name    : PositivityTheory.KReal.Harm.rename_first_lowering
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:41:44.936151+00:00
-- url     : https://prove2.me/theorems/f674cf70-d137-431b-a511-45da497cb124
-- title:
--   Harm: rename first lowering
-- statement:
--   The Harm construction uses the rename first lowering property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreHarm.lean#L150-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreHarm.lean#L150-L163

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
open PI.FockOneDegW.Swap

theorem PositivityTheory.KReal.Harm.rename_first_lowering (a b : Ix p q) (P : Pol p q r s) :
    rename (sw p q r s) (low1 a b P) =
      PI.FockOneDegW.lowOp (p := r) (q := s) a b (rename (sw p q r s) P) := by sorry
