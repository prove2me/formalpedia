-- Prove2me | Theorems.Thm_PositivityTheory_KReal_mem_polChi_iff_hw
-- name    : PositivityTheory.KReal.mem_polChi_iff_hw
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:30:52.865804+00:00
-- url     : https://prove2.me/theorems/36067a68-7f27-5f2c-bcf6-ee1bf77da781
-- title:
--   KReal: mem pol Chi iff hw
-- statement:
--   The KReal construction uses the mem pol Chi iff hw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreLie.lean#L226-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreLie.lean#L226-L236

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCyc
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreLie
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

theorem PositivityTheory.KReal.mem_polChi_iff_hw (c : ℂ) (c0 : ℚ) (hc : c = c0) (x : Pol p q r s) :
    x ∈ polChi p q r s c ↔ x ∈ hwSub (fockAct1 p q r s) (fun _ => c0) := by sorry
