-- Prove2me | Theorems.Thm_PositivityTheory_CW_SecondMomentAlgebra_zsum
-- name    : PositivityTheory.CW.SecondMomentAlgebra.zsum
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:52:23.976847+00:00
-- url     : https://prove2.me/theorems/71837af7-2007-5173-9b5d-06882e044894
-- title:
--   Second Moment Algebra: zsum
-- statement:
--   The Second Moment Algebra construction uses the zsum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/MatrixActionSingle.lean#L47-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/MatrixActionSingle.lean#L47-L54

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_MatrixActionSingle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
open PositivityTheory.CW.SecondMomentAlgebra
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem PositivityTheory.CW.SecondMomentAlgebra.zsum {n : ℕ} (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V)
    (hZc : ∀ a b, ε a = ε b → Z ε E a b = 0) (w : V) :
    ∑ c, ∑ d, ‖Z ε E c d w‖ ^ 2 = ∑ p ∈ nc ε, ‖Z ε E p.1 p.2 w‖ ^ 2 := by sorry
