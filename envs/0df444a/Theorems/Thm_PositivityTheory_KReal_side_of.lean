-- Prove2me | Theorems.Thm_PositivityTheory_KReal_side_of
-- name    : PositivityTheory.KReal.side_of
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:33:14.295694+00:00
-- url     : https://prove2.me/theorems/ae309fbd-9e3f-509b-9a32-0bbf26cd81a4
-- title:
--   KReal: side of
-- statement:
--   The KReal construction uses the side of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreSide.lean#L159-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreSide.lean#L159-L211

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreStar
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreGen
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreSide
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
open GoodSideLattices

theorem PositivityTheory.KReal.side_of {p q r s : ℕ} (c τ : ℂ) (c0 τ0 : ℚ) (hc : c = c0) (hτ : τ = τ0) (La : Ix r s → ℚ)
    (hC : CombOK p q c0 τ0 La) (hN : Nontrivial (ThC p q r s c)) :
    Side (fun x => La x + τ0) (ThC p q r s c) (thAct p q r s c τ) := by sorry
