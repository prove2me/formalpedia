-- Prove2me | Theorems.Thm_PositivityTheory_KReal_jHarmonic_stable_first_action
-- name    : PositivityTheory.KReal.jHarmonic_stable_first_action
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:40:41.416646+00:00
-- url     : https://prove2.me/theorems/c0d78487-cc6b-428a-9b8a-c1e747f06ccc
-- title:
--   KReal: j Harmonic stable first action
-- statement:
--   The KReal construction uses the j Harmonic stable first action property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreHarm.lean#L267-L272
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreHarm.lean#L267-L272

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
open Harm
variable {p q r s : ℕ}

theorem PositivityTheory.KReal.jHarmonic_stable_first_action : KSt (units (fockAct1 p q r s)) (jHarm p q r s) := by sorry
