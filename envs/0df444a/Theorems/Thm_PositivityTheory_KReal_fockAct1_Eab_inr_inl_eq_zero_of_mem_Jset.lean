-- Prove2me | Theorems.Thm_PositivityTheory_KReal_fockAct1_Eab_inr_inl_eq_zero_of_mem_Jset
-- name    : PositivityTheory.KReal.fockAct1_Eab_inr_inl_eq_zero_of_mem_Jset
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:38:46.762802+00:00
-- url     : https://prove2.me/theorems/4de2b3e9-3e2a-56c0-88c5-eab2fd653172
-- title:
--   KReal: fock Act1 Eab inr inl eq zero of mem Jset
-- statement:
--   The KReal construction uses the fock Act1 Eab inr inl eq zero of mem Jset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CorePair.lean#L50-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CorePair.lean#L50-L58

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreLie
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CorePair
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

theorem PositivityTheory.KReal.fockAct1_Eab_inr_inl_eq_zero_of_mem_Jset {p q r : ℕ} {x : Pol p q r 0} (hx : x ∈ Jset p q r 0) (i : Fin p) (j : Fin q) :
    fockAct1 p q r 0 (Eab (.inr j) (.inl i)) x = 0 := by sorry
