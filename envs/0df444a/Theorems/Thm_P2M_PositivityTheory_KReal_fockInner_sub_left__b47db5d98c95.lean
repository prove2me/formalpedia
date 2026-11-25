-- Prove2me | Theorems.Thm_P2M_PositivityTheory_KReal_fockInner_sub_left__b47db5d98c95
-- name    : P2M_PositivityTheory_KReal_fockInner_sub_left__b47db5d98c95
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:45:51.062716+00:00
-- url     : https://prove2.me/theorems/82655eac-e889-5522-a76a-86a468cb8ddb
-- title:
--   P2 M Positivity Theory KReal fock Inner sub left  b47db5d98c95: P2 M Positivity Theory KReal fock Inner sub left  b47db5d98c95
-- statement:
--   The P2 M Positivity Theory KReal fock Inner sub left  b47db5d98c95 construction uses the P2 M Positivity Theory KReal fock Inner sub left  b47db5d98c95 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreNonv.lean#L139-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreNonv.lean#L139-L141

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreGraph
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDelta
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreProj
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreNonv
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
variable {p q r s : ℕ}

theorem P2M_PositivityTheory_KReal_fockInner_sub_left__b47db5d98c95 (P P' Q : Pol p q r s) :
    fockInner (P - P') Q = fockInner P Q - fockInner P' Q := by sorry

alias «PositivityTheory».«KReal».«fockInner_sub_left'» := P2M_PositivityTheory_KReal_fockInner_sub_left__b47db5d98c95
