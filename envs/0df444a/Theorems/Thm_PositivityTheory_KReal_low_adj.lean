-- Prove2me | Theorems.Thm_PositivityTheory_KReal_low_adj
-- name    : PositivityTheory.KReal.low_adj
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:30:46.508621+00:00
-- url     : https://prove2.me/theorems/eed39efc-1736-5067-87d6-80fce78c3c16
-- title:
--   KReal: low adj
-- statement:
--   The KReal construction uses the low adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreLie.lean#L78-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreLie.lean#L78-L85

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

theorem PositivityTheory.KReal.low_adj (l : Ln p q r s) (P Q : Pol p q r s) :
    fockInner (lowB l P) Q = sgnC l * fockInner P (raiB l Q) := by sorry
